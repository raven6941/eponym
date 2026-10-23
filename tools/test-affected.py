#!/usr/bin/env python3
"""tools/test-affected.py — run only the CI steps affected by local changes.

Issue #405. Dev-loop accelerator: the full matrix (tools/ci-local.sh)
remains the merge gate; this tool selects the affected subset of its steps
so most edits re-run in minutes instead of ~24.

How it works
------------
1. Enumerate steps: ``EPONYM_LIST_STEPS=1 sh tools/ci-local.sh`` prints every
   step's command (the single source of truth for the matrix — nothing is
   duplicated here).
2. For each step, compute the files it depends on:
   * Nim import closure — ``import``/``from``/``include``/``export``
     statements are parsed and resolved against the step's ``--path`` flags
     (P or XP, mirroring ci-local.sh). Unresolvable non-stdlib imports make
     the driver depend on everything (fail-safe; the --self-test asserts
     this never happens on a clean tree).
   * Macro-time ``.ep`` inputs — the eponymBlock macro reads ``import
     "x.ep"`` files at compile time, so quoted ``.ep`` references in driver
     sources are resolved (relative to the referencing file) and followed
     transitively through ``import`` statements inside ``.ep`` files.
     A reference that resolves to no file is kept as a literal path so a
     *deleted* ``.ep`` file still matches.
   * Quoted ``tests/fixtures/*.nim`` references (drivers that shell out to
     ``nim c`` on fixture files) pull in the fixture plus its own closure.
   * Directory-walk steps: ``run_examples`` walks ``lib/``, ``examples/``,
     ``examples/ep/``; ``run_embedded_examples`` walks
     ``examples/embedded/``; the prelude-install script installs the whole
     package (``src/**``, ``lib/**``) and extracts ``docs/tutorial.md``
     snippets; the vscode smoke step builds ``src/eponym/lsp.nim`` and
     exercises ``editors/vscode`` and ``examples/embedded/sheds_demo.nim``.
3. Changed files come from ``git diff --name-only <base>`` plus untracked
   (non-ignored) files. A step runs if any changed file is in its
   dependency set. Anything that cannot be classified (build config,
   ``tools/``, ``.github/``, ...) selects every step — false negatives are
   the failure mode this is designed against; false positives just cost
   time. ``bench/`` and documentation (except ``docs/tutorial.md``, which
   the prelude script reads) select nothing: nothing in CI reads them.

Usage
-----
  sh tools/test-affected.sh [--base REF] [--changed PATH]... [--all]
                            [--dry-run] [--verbose] [--self-test]

  --base REF      git ref to diff against (default: main)
  --changed PATH  repeatable; bypass git change detection (debugging aid)
  --all           run the full matrix (same as tools/ci-local.sh)
  --dry-run       print the plan without running anything
  --verbose       also list skipped steps
  --self-test     validate the mapping model against the issue's acceptance
                  criteria; exits non-zero on failure
"""

import os
import re
import shlex
import shutil
import subprocess
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# ---------------------------------------------------------------------------
# Path sets, mirroring the $P / $XP variables in tools/ci-local.sh

PATH_SETS = {
    "P": ["tests", "src", "src/eponym"],
    "XP": ["tests", "src", "src/eponym",
           "src/experimental", "src/experimental/relational",
           "src/experimental/staging"],
    # tests/repl_session.sh builds src/repl.nim with its own flags
    # (src/relational and src/staging no longer exist; harmless if absent)
    "REPL": ["src", "src/eponym", "src/relational", "src/staging"],
}
# Resolution order for a non-relative import: importer's dir first (a
# superset of nim's lookup — can only add deps, never drop them), then P,
# then the XP extras.
RESOLVE_DIRS = (["{impdir}"] + PATH_SETS["P"] +
                [d for d in PATH_SETS["XP"] if d not in PATH_SETS["P"]])

# Bare module names that resolve outside the repo (Nim stdlib, plus the
# test-only third-party lib installed by ci-local.sh). Anything else that
# fails to resolve is reported, and the importing driver is treated as
# depending on everything (fail-safe).
EXTERNAL_BARE = {
    "algorithm", "cgi", "colors", "complex", "critbits", "db_common",
    "distros", "dynlib", "encodings", "fenv", "hashes", "htmlgen",
    "htmlparser", "httpclient", "json", "lenientops", "logging", "macros",
    "marshal", "math", "md5", "memfiles", "mersenne", "net",
    "nativesockets", "options", "os", "osproc", "parsecfg", "parsecsv",
    "parsejson", "parseopt", "parsesql", "parseutils", "parsexml",
    "pathnorm", "pegs", "posix", "punycode", "random", "rationals", "re",
    "rlocks", "segfaults", "selectors", "sequtils", "sets", "sha1", "smtp",
    "stats", "strformat", "streams", "strmisc", "strscans", "strtabs",
    "strutils", "sugar", "sysrand", "tables", "terminal", "threadpool",
    "times", "typetraits", "unicode", "unidecode", "uri", "volatile",
    "xmlparser", "xmltree", "falsify",
}

UNRESOLVED = "<unresolved>"


# ---------------------------------------------------------------------------
# Nim import parsing

_re_from = re.compile(r"^\s*from\s+([A-Za-z0-9_./]+)\s+import\b")
_re_stmt = re.compile(r"^\s*(?:import|include|export)\s+(.+?)\s*$")
_re_alias = re.compile(r"\s+as\s+[A-Za-z_]\w*$")


def _split_import_list(s):
    """Split 'a, b, p/[c, d]' into ['a', 'b', 'p/c', 'p/d']."""
    parts, cur, depth = [], "", 0
    for ch in s:
        if ch == "[":
            depth += 1
            cur += ch
        elif ch == "]":
            depth -= 1
            cur += ch
        elif ch == "," and depth == 0:
            parts.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur.strip())
    out = []
    for p in parts:
        p = _re_alias.sub("", p).strip()
        m = re.match(r"^(.+?)/\[([^\]]+)\]$", p)
        if m:
            prefix = m.group(1)
            out.extend(prefix + "/" + x.strip() for x in m.group(2).split(","))
        else:
            out.append(p)
    return [x for x in out if x]


def resolve_nim(mod, importer):
    """Resolve an imported module to a repo-relative path, None if external,
    UNRESOLVED if it looks internal but no file was found."""
    mod = mod.strip().strip('"')
    if not mod:
        return None
    if mod.startswith("std/") or ("/" not in mod and mod in EXTERNAL_BARE):
        return None
    impdir = os.path.dirname(importer)
    cands = []
    if mod.startswith("."):
        cands.append(os.path.normpath(os.path.join(impdir, mod)) + ".nim")
    else:
        for d in RESOLVE_DIRS:
            d = d.format(impdir=impdir)
            cands.append(os.path.normpath(os.path.join(d, mod)) + ".nim")
    seen = set()
    for c in cands:
        if c in seen:
            continue
        seen.add(c)
        if os.path.isfile(os.path.join(REPO, c)):
            return c
    return UNRESOLVED


_direct_nim_cache = {}


def direct_nim_deps(relpath):
    """Parse one .nim file. Returns (resolved_deps, unresolved_mods)."""
    if relpath in _direct_nim_cache:
        return _direct_nim_cache[relpath]
    deps, unresolved = [], []
    try:
        with open(os.path.join(REPO, relpath), encoding="utf-8") as f:
            lines = f.readlines()
    except OSError:
        result = ([], ["<unreadable: %s>" % relpath])
        _direct_nim_cache[relpath] = result
        return result
    for line in lines:
        code = line.split("#", 1)[0]
        mods = []
        m = _re_from.match(code)
        if m:
            mods = [m.group(1)]
        else:
            m = _re_stmt.match(code)
            if m:
                mods = _split_import_list(m.group(1))
        for mod in mods:
            # `import "x.ep"` inside eponymBlock bodies is a surface-language
            # import read by the macro at compile time, not a Nim import —
            # the .ep machinery (source_ep_refs) tracks those.
            if mod.strip().strip('"').endswith(".ep"):
                continue
            r = resolve_nim(mod, relpath)
            if r is None:
                continue
            if r == UNRESOLVED:
                unresolved.append("%s (from %s)" % (mod, relpath))
            else:
                deps.append(r)
    result = (deps, unresolved)
    _direct_nim_cache[relpath] = result
    return result


def nim_closure(entry):
    """Transitive Nim import closure of entry (repo-relative paths)."""
    seen, stack, unresolved = set(), [entry], set()
    while stack:
        f = stack.pop()
        if f in seen:
            continue
        seen.add(f)
        deps, unres = direct_nim_deps(f)
        unresolved.update(unres)
        stack.extend(d for d in deps if d not in seen)
    return seen, unresolved


# ---------------------------------------------------------------------------
# .ep dependency tracking (macro-time inputs)

_re_ep_quoted = re.compile(r'"((?:\.\./)*(?:lib|examples|tests)/[^"]*\.ep)"')
_re_ep_bare = re.compile(r"(?<![\w/.-])((?:lib|examples|tests)/[^\s\"')\]]*\.ep)")
_re_ep_import = re.compile(r'^\s*import\s+"([^"]+)"')
_re_nim_quoted = re.compile(r'"((?:tests|examples|lib)/[^"]*\.nim)"')


def _resolve_ep(ref, containing):
    """Resolve an .ep reference to repo-relative path; keep the literal
    normalized path when the file is missing (covers deletions)."""
    ref = os.path.normpath(ref)
    if os.path.isfile(os.path.join(REPO, ref)):
        return ref
    alt = os.path.normpath(os.path.join(os.path.dirname(containing), ref))
    if os.path.isfile(os.path.join(REPO, alt)):
        return alt
    return ref


_ep_file_cache = {}


def ep_file_imports(ep_relpath):
    """Direct `import "..."` edges inside one .ep file."""
    if ep_relpath in _ep_file_cache:
        return _ep_file_cache[ep_relpath]
    out = []
    try:
        with open(os.path.join(REPO, ep_relpath), encoding="utf-8") as f:
            for line in f:
                m = _re_ep_import.match(line)
                if m:
                    out.append(_resolve_ep(m.group(1), ep_relpath))
    except OSError:
        pass
    _ep_file_cache[ep_relpath] = out
    return out


def source_ep_refs(relpath):
    """Quoted/bare .ep paths referenced by a .nim or .sh source file."""
    try:
        with open(os.path.join(REPO, relpath), encoding="utf-8",
                   errors="replace") as f:
            text = f.read()
    except OSError:
        return []
    refs = _re_ep_quoted.findall(text) + _re_ep_bare.findall(text)
    return [_resolve_ep(r, relpath) for r in refs]


def ep_closure(entry_source):
    """Transitive .ep inputs of a source file (compile-time macro reads)."""
    seen, stack = set(), source_ep_refs(entry_source)
    while stack:
        f = stack.pop()
        if f in seen:
            continue
        seen.add(f)
        stack.extend(e for e in ep_file_imports(f) if e not in seen)
    return seen


def source_nim_refs(relpath):
    """Quoted tests/.../*.nim paths in a source file (drivers that shell out
    to `nim c` on fixture files); each pulls in its own Nim closure."""
    try:
        with open(os.path.join(REPO, relpath), encoding="utf-8",
                   errors="replace") as f:
            text = f.read()
    except OSError:
        return set()
    out = set()
    for r in _re_nim_quoted.findall(text):
        r = os.path.normpath(r)
        if os.path.isfile(os.path.join(REPO, r)):
            out.add(r)
    return out


# ---------------------------------------------------------------------------
# Steps

class Step:
    def __init__(self, idx, cmd):
        self.idx = idx          # 1-based, matches ci-local.sh step order
        self.cmd = cmd
        self.kind = None        # 'nim' | 'sh'
        self.driver = None      # repo-relative .nim / .sh path
        self.pset = "P"
        self.nim_deps = set()   # repo-relative paths (Nim closure)
        self.ep_deps = set()    # repo-relative .ep paths
        self.extra = set()      # literal extra file deps
        self.flags = set()      # 'src_all' | 'lib_all' | 'all'
        self.reasons = []       # (changed_file, why)
        self.unresolved = []    # unresolved imports (fail-safe: always run)


def list_steps():
    env = dict(os.environ)
    env["EPONYM_LIST_STEPS"] = "1"
    env.pop("EPONYM_CI_SHARD", None)
    p = subprocess.run(["sh", "tools/ci-local.sh"], cwd=REPO, env=env,
                       capture_output=True, text=True)
    if p.returncode != 0:
        sys.stderr.write("step listing failed:\n%s\n" % p.stderr)
        sys.exit(2)
    steps = []
    for line in p.stdout.splitlines():
        if not line.startswith("STEP: "):
            continue
        steps.append(Step(len(steps) + 1, line[len("STEP: "):].strip()))
    return steps


def parse_step(step):
    toks = shlex.split(step.cmd)
    if not toks:
        return False
    if toks[0] == "nim":
        nimfile = next((t for t in toks if t.endswith(".nim")), None)
        if nimfile is None:
            return False
        step.kind = "nim"
        step.driver = os.path.normpath(nimfile)
        step.pset = "XP" if any("src/experimental" in t for t in toks) else "P"
        return True
    if toks[0] == "sh" and len(toks) > 1:
        step.kind = "sh"
        step.driver = os.path.normpath(toks[1])
        return True
    return False


def compute_step_deps(step):
    if step.kind == "nim":
        step.nim_deps, unres = nim_closure(step.driver)
        step.unresolved = sorted(unres)
        step.ep_deps = ep_closure(step.driver)
        for ref in source_nim_refs(step.driver):
            fdeps, funres = nim_closure(ref)
            step.nim_deps |= fdeps
            step.unresolved.extend(sorted(funres))
            step.ep_deps |= ep_closure(ref)
    elif step.kind == "sh":
        step.extra.add(step.driver)
        step.ep_deps = ep_closure(step.driver)
        if step.driver == "tests/repl_session.sh":
            deps, unres = nim_closure("src/repl.nim")
            step.nim_deps |= deps
            step.unresolved = sorted(unres)
            step.nim_deps.add("src/repl.nim")
        elif step.driver == "tests/test_trust_report.sh":
            deps, unres = nim_closure("tests/test_runtime_value_bridge.nim")
            step.nim_deps |= deps
            step.unresolved = sorted(unres)
        elif step.driver == "tests/test_package_prelude_install.sh":
            # Installs the whole package and elaborates the prelude: any
            # src/ or lib/ change, the nimble metadata, or the tutorial
            # snippets it extracts can affect it.
            step.flags.add("src_all")
            step.flags.add("lib_all")
            step.extra.add("eponym.nimble")
            step.extra.add("docs/tutorial.md")
        elif step.driver == "tools/vscode-smoke.sh":
            deps, unres = nim_closure("src/eponym/lsp.nim")
            step.nim_deps |= deps
            step.unresolved = sorted(unres)
            step.extra.add("examples/embedded/sheds_demo.nim")
            step.flags.add("editors_all")
    if step.unresolved:
        # Fail-safe: the closure is incomplete, so the step always runs.
        step.flags.add("all")


# ---------------------------------------------------------------------------
# Change detection and classification

def git_changed(base):
    p = subprocess.run(["git", "diff", "--name-only", base, "--", "."],
                       cwd=REPO, capture_output=True, text=True)
    if p.returncode != 0:
        sys.stderr.write("git diff failed for base %r\n" % base)
        sys.exit(2)
    changed = {l.strip() for l in p.stdout.splitlines() if l.strip()}
    p = subprocess.run(["git", "ls-files", "--others", "--exclude-standard"],
                       cwd=REPO, capture_output=True, text=True)
    changed.update(l.strip() for l in p.stdout.splitlines() if l.strip())
    return sorted(changed)


def resolve_base(base):
    for cand in ([base] if base != "main" else ["main", "origin/main"]):
        p = subprocess.run(["git", "rev-parse", "--verify", "--quiet", cand],
                           cwd=REPO, capture_output=True, text=True)
        if p.returncode == 0:
            return cand
    sys.stderr.write("base ref %r not found (tried main, origin/main)\n" % base)
    sys.exit(2)


INERT_SUFFIXES = (".md",)
INERT_PREFIXES = ("bench/", "docs/", ".vscode/")
INERT_FILES = {".gitignore", ".gitattributes", "LICENSE", "LICENSE.md"}
ALL_PREFIXES = ("tools/", ".github/")
ALL_SUFFIXES = (".cfg", ".nims")
ALL_FILES = {"eponym.nimble"}

# run_examples walks these at runtime; a change under any of them selects it
WALK_DIRS_RUN_EXAMPLES = ("lib/", "examples/", "examples/ep/")
WALK_DIRS_RUN_EMBEDDED = ("examples/embedded/",)


def match_step(step, changed):
    """Why does `changed` select `step`? Returns a reason string or None."""
    if "all" in step.flags:
        return "fail-safe: unresolved imports" if step.unresolved else \
            "tooling/config change"
    c = changed
    if c in step.extra:
        return "step input"
    if c.endswith(".nim") and c in step.nim_deps:
        return "Nim import closure"
    if c.endswith(".ep"):
        if c in step.ep_deps:
            return ".ep import closure"
        if (c.startswith(WALK_DIRS_RUN_EXAMPLES) and
                step.driver == "tests/run_examples.nim"):
            return "directory walk (lib/examples)"
    else:
        if (c.startswith(WALK_DIRS_RUN_EMBEDDED) and
                step.driver == "tests/run_embedded_examples.nim"):
            return "directory walk (examples/embedded)"
        if (c.startswith(WALK_DIRS_RUN_EXAMPLES) and
                step.driver == "tests/run_examples.nim"):
            return "directory walk (lib/examples)"
    if "src_all" in step.flags and (c == "src" or c.startswith("src/")):
        return "installed package contents"
    if "lib_all" in step.flags and (c == "lib" or c.startswith("lib/")):
        return "installed prelude"
    if "editors_all" in step.flags and c.startswith("editors/"):
        return "vscode extension sources"
    return None


def classify(changed):
    """'inert' | 'all' | 'dep' — how to treat a changed path."""
    if changed in INERT_FILES or changed.endswith(INERT_SUFFIXES) \
            or changed.startswith(INERT_PREFIXES):
        if changed == "docs/tutorial.md":
            return "dep"  # read by the prelude-install script
        return "inert"
    if changed in ALL_FILES or changed.startswith(ALL_PREFIXES) \
            or changed.endswith(ALL_SUFFIXES):
        return "all"
    return "dep"


def select(steps, changed_files):
    for step in steps:
        step.reasons = []
    for c in changed_files:
        kind = classify(c)
        if kind == "inert":
            continue
        if kind == "all":
            for step in steps:
                step.reasons.append((c, "tooling/config change"))
            continue
        for step in steps:
            why = match_step(step, c)
            if why:
                step.reasons.append((c, why))
    return [s for s in steps if s.reasons], [s for s in steps if not s.reasons]


# ---------------------------------------------------------------------------
# Execution

def ensure_nim():
    if shutil.which("nim") is None:
        sys.stderr.write(
            "nim not on PATH. Prefix with:\n"
            '  export PATH="$HOME/.nimble/bin:$PATH"\n'
            "(see TOOLS.md: Nim toolchain)\n")
        sys.exit(2)


def ensure_falsify():
    # Same prelude as ci-local.sh: PBT suites need it on the import path.
    p = subprocess.run(["nimble", "path", "falsify"],
                       capture_output=True, text=True)
    if p.returncode != 0:
        print("### installing falsify (as ci-local.sh does)")
        r = subprocess.run(
            ["nimble", "install", "-y",
             "https://github.com/raven6941/falsify"], cwd=REPO)
        if r.returncode != 0:
            sys.exit(r.returncode)


def describe(step):
    if step.kind == "nim":
        return step.driver
    if step.kind == "sh":
        return step.driver
    return step.cmd


def print_plan(affected, skipped, changed_files, verbose):
    print("changed files: %d" % len(changed_files))
    for c in changed_files:
        print("  %s" % c)
    print("affected: %d step(s)" % len(affected))
    for s in affected:
        why = "; ".join("%s (%s)" % (c, w) for c, w in s.reasons[:3])
        if len(s.reasons) > 3:
            why += "; +%d more" % (len(s.reasons) - 3)
        print("  step %d: %s\n      <- %s" % (s.idx, describe(s), why))
    print("skipped: %d step(s)" % len(skipped))
    if verbose:
        for s in skipped:
            print("  step %d: %s" % (s.idx, describe(s)))


def run_steps(affected):
    for s in affected:
        print("=== step %d: %s ===" % (s.idx, s.cmd), flush=True)
        r = subprocess.run(shlex.split(s.cmd), cwd=REPO)
        if r.returncode != 0:
            print("step %d FAILED (exit %d): %s" %
                  (s.idx, r.returncode, s.cmd), file=sys.stderr)
            return r.returncode
    print("### AFFECTED-ONLY RUN PASSED (%d steps)" % len(affected))
    return 0


# ---------------------------------------------------------------------------
# Self-test: the issue's acceptance criteria as executable checks

def self_test(steps):
    failures = []

    def check(name, cond, detail=""):
        print(("PASS " if cond else "FAIL ") + name +
              (" — " + detail if detail and not cond else ""))
        if not cond:
            failures.append(name)

    check("steps enumerated", len(steps) > 50, "got %d" % len(steps))
    bad = [s for s in steps if s.kind not in ("nim", "sh")]
    check("every step parsed", not bad,
          "unparsed: %s" % [s.cmd for s in bad][:3])

    # Closure health: no unresolved imports anywhere on the clean tree.
    all_unres = sorted({u for s in steps for u in s.unresolved})
    check("no unresolved imports", not all_unres, str(all_unres[:5]))

    def selected_for(changed):
        aff, _ = select(steps, changed)
        return aff

    def by_driver(name):
        return [s for s in steps if s.driver == name]

    # Acceptance 1: a leaf-test change runs that driver plus true dependents.
    leaf = selected_for(["tests/test_mutual_termination.nim"])
    leaf_drivers = {s.driver for s in leaf}
    check("leaf test selects its own step",
          "tests/test_mutual_termination.nim" in leaf_drivers,
          str(sorted(leaf_drivers)))
    check("leaf test stays small", len(leaf) <= 4,
          "%d steps: %s" % (len(leaf), sorted(leaf_drivers)))

    # Acceptance 2: src/eponym/elab.nim selects (nearly) all drivers.
    elab = selected_for(["src/eponym/elab.nim"])
    frac = len(elab) / max(len(steps), 1)
    check("elab.nim selects nearly all steps", frac >= 0.6,
          "%.0f%% (%d/%d)" % (100 * frac, len(elab), len(steps)))

    # Acceptance 3: lib/*.ep selects the embedded/eponym drivers.
    bool_ep = selected_for(["lib/bool.ep"])
    bool_drivers = {s.driver for s in bool_ep}
    check("lib/bool.ep selects test_erasure (imports it)",
          "tests/test_erasure.nim" in bool_drivers)
    check("lib/bool.ep selects run_examples (walks lib/)",
          "tests/run_examples.nim" in bool_drivers)
    check("lib/bool.ep selects prelude-install (installs lib/)",
          "tests/test_package_prelude_install.sh" in bool_drivers)
    check("lib/bool.ep does not select an unrelated suite",
          "tests/test_mutual_termination.nim" not in bool_drivers)
    check("lib/bool.ep stays selective",
          len(bool_ep) < len(steps) // 2,
          "%d/%d steps" % (len(bool_ep), len(steps)))

    # Special steps are wired.
    smoke = by_driver("tools/vscode-smoke.sh")
    check("vscode smoke step present", len(smoke) == 1)
    if smoke:
        aff, _ = select(steps, ["editors/vscode/package.json"])
        check("editors/vscode change selects smoke",
              smoke[0] in aff)
        aff, _ = select(steps, ["examples/embedded/sheds_demo.nim"])
        check("sheds_demo change selects smoke", smoke[0] in aff)
    prelude = by_driver("tests/test_package_prelude_install.sh")
    if prelude:
        aff, _ = select(steps, ["docs/tutorial.md"])
        check("docs/tutorial.md selects prelude-install", prelude[0] in aff)
    inert, _ = select(steps, ["README.md", "docs/known-limitations.md"])
    check("docs changes select nothing", not inert,
          str([s.driver for s in inert][:3]))

    print("%d check(s) failed" % len(failures) if failures
          else "self-test: all checks passed")
    return 1 if failures else 0


# ---------------------------------------------------------------------------
# CLI

def main(argv):
    base, changed_override = "main", []
    dry_run = verbose = force_all = do_self_test = False
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--base":
            i += 1
            base = argv[i]
        elif a == "--changed":
            i += 1
            p = argv[i]
            changed_override.append(os.path.normpath(p)
                                    if not os.path.isabs(p)
                                    else os.path.relpath(p, REPO))
        elif a == "--all":
            force_all = True
        elif a == "--dry-run":
            dry_run = True
        elif a == "--verbose":
            verbose = True
        elif a == "--self-test":
            do_self_test = True
        elif a in ("-h", "--help"):
            print(__doc__)
            return 0
        else:
            sys.stderr.write("unknown arg: %s\n" % a)
            return 2
        i += 1

    steps = list_steps()
    for s in steps:
        if not parse_step(s):
            sys.stderr.write("cannot parse step %d: %s\n" % (s.idx, s.cmd))
            return 2
        compute_step_deps(s)

    if do_self_test:
        return self_test(steps)

    ensure_nim()

    if force_all:
        affected, skipped = steps, []
        changed_files = ["<forced: --all>"]
    else:
        if changed_override:
            changed_files = changed_override
        else:
            changed_files = git_changed(resolve_base(base))
        affected, skipped = select(steps, changed_files)

    if not changed_override and not force_all and not changed_files:
        print("no changes vs %s: nothing to run" % base)
        return 0

    print_plan(affected, skipped, changed_files, verbose)
    if dry_run or not affected:
        return 0
    ensure_falsify()
    return run_steps(affected)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
