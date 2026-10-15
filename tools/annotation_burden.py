#!/usr/bin/env python3
"""Issue #103: annotation-burden measurement runner.

Tokenizes Eponym surface files with a lexer mirroring `src/eponym/parse_surf.nim`
and reports, per file and in total:

  total tokens  vs  annotation tokens  (ratio)

Annotation-token rules (documented; applied uniformly so the ratio is a
comparable baseline across measurements):

  1. `proc` return-type ascriptions: the `:` plus the type tokens up to `=`.
     (A proc's declared return type ascribes its body.)
  2. Term ascriptions `(e : T)`: the `:` plus the tokens of `T`.
     Distinguished from binder groups `(x : T)` / `(0 x : T)` / `{x : T}` /
     `(x : A) -> B` by shape: a group whose top-level tokens start with
     `[quantity-marker] <ident> :` is a binder, not an ascription.
  3. Quantity annotations: the `0` / `1` / quantity-variable marker in a
     binder group counts 1 token. (Unannotated binders use quantity
     inference since #84 and cost nothing here.)
  4. `the`-style casts: the keyword `the` counts 1. (No `the` in the
     grammar yet; the counter exists so the category is not forgotten.)
  5. Explicit arguments for `{x : T}` implicit binders are *not* separately
     countable at token level (application is positional juxtaposition);
     they are subsumed in total tokens. Documented limitation.

Binder domain types `(x : T)` are NOT annotation tokens: the grammar
requires them, so they are the baseline of "what must be written".

Elaboration failure sites that required human repair are recorded by hand in
`FAILURE_SITES.md` next to the corpus; this script prints that count
alongside the token ratio.

Usage:
    python3 tools/annotation_burden.py examples/ep/corpus103/
"""

import os
import re
import sys

KEYWORDS = {
    "data", "proc", "def", "postulate", "elim", "red", "record",
    "import", "interface", "command", "where",
    "lam", "Pi", "Sig", "let", "in", "fst", "snd", "by",
    "clause", "field",
}

PUNCT2 = {":=", "->", "<>"}
PUNCT1 = set("():{},[]|?.=,")


def lex(src):
    """Token list mirroring parse_surf.lex (comments and whitespace dropped)."""
    toks = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c == "#":
            while i < n and src[i] != "\n":
                i += 1
            continue
        if c.isspace():
            i += 1
            continue
        if c == '"':
            j = i + 1
            while j < n and src[j] != '"':
                if src[j] == "\\":
                    j += 1
                j += 1
            toks.append(src[i:j + 1])
            i = j + 1
            continue
        if c.isalpha() or c == "_":
            j = i
            while j < n and (src[j].isalnum() or src[j] in "_'"):
                j += 1
            toks.append(src[i:j])
            i = j
            continue
        if c.isdigit():
            j = i
            while j < n and src[j].isdigit():
                j += 1
            toks.append(src[i:j])
            i = j
            continue
        if src[i:i + 2] in PUNCT2:
            toks.append(src[i:i + 2])
            i += 2
            continue
        if c in PUNCT1:
            toks.append(c)
            i += 1
            continue
        # anything else (shouldn't happen in valid sources): single char
        toks.append(c)
        i += 1
    return toks


def is_ident(t):
    return re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", t) is not None


def is_qty_marker(t):
    return t in ("0", "1") or (is_ident(t) and t not in KEYWORDS)


def matching(toks, open_i):
    """Index of the token matching the bracket at open_i."""
    pairs = {"(": ")", "{": "}", "[": "]"}
    close = pairs[toks[open_i]]
    depth = 0
    for i in range(open_i, len(toks)):
        if toks[i] == toks[open_i]:
            depth += 1
        elif toks[i] == close:
            depth -= 1
            if depth == 0:
                return i
    return None


def top_level_colon(toks, open_i, close_i):
    """Index of a top-level ':' inside the group, or None."""
    depth = 0
    pairs = {"(": ")", "{": "}", "[": "]"}
    opens = set(pairs)
    closes = set(pairs.values())
    for i in range(open_i + 1, close_i):
        t = toks[i]
        if t in opens:
            depth += 1
        elif t in closes:
            depth -= 1
        elif t == ":" and depth == 0:
            return i
    return None


def looks_like_binder(toks, open_i, close_i):
    """Group shape `[qty] <ident> : ...` at top level -> binder, not ascription."""
    inner = []
    depth = 0
    pairs = {"(": ")", "{": "}", "[": "]"}
    opens = set(pairs)
    closes = set(pairs.values())
    for i in range(open_i + 1, close_i):
        t = toks[i]
        if t in opens:
            depth += 1
        elif t in closes:
            depth -= 1
        if depth == 0:
            inner.append(t)
    if not inner:
        return False
    k = 0
    if len(inner) >= 3 and is_qty_marker(inner[0]) and is_ident(inner[1]) and inner[2] == ":":
        return True  # (0 x : T) / (1 x : T) / (q x : T)
    if len(inner) >= 2 and is_ident(inner[0]) and inner[1] == ":":
        return True  # (x : T) / {x : T}
    return False


def count_file(path):
    with open(path) as f:
        src = f.read()
    toks = lex(src)
    total = len(toks)
    ann = 0
    detail = {"proc_ret": 0, "ascription": 0, "quantity": 0, "the": 0}

    i = 0
    while i < len(toks):
        t = toks[i]
        if t == "the" and is_ident(t):
            detail["the"] += 1
            ann += 1
        elif t == "proc":
            # proc name tele... : Ret =  -> count ':' and Ret tokens
            j = i + 1
            depth = 0
            while j < len(toks):
                tj = toks[j]
                if tj in "({[":
                    depth += 1
                elif tj in ")}]":
                    depth -= 1
                elif tj == ":" and depth == 0:
                    break
                elif tj == "=" and depth == 0:
                    j = None
                    break
                j += 1
            if j is not None:
                k = j + 1
                depth = 0
                while k < len(toks):
                    tk = toks[k]
                    if tk in "({[":
                        depth += 1
                    elif tk in ")}]":
                        depth -= 1
                    elif tk == "=" and depth == 0:
                        break
                    k += 1
                n = 1 + (k - (j + 1))  # ':' plus Ret tokens
                detail["proc_ret"] += n
                ann += n
        elif t in ("(", "{"):
            close_i = matching(toks, i)
            if close_i is not None:
                if looks_like_binder(toks, i, close_i):
                    # quantity marker?
                    nxt = toks[i + 1]
                    if (is_qty_marker(nxt) and close_i - i >= 4
                            and is_ident(toks[i + 2]) and toks[i + 3] == ":"):
                        # (0 x : T) or (1 x : T) or (q x : T); plain (x : T)
                        # has no marker.
                        if not (is_ident(nxt) and toks[i + 2] == ":"):
                            detail["quantity"] += 1
                            ann += 1
                else:
                    ci = top_level_colon(toks, i, close_i)
                    if ci is not None:
                        n = 1 + (close_i - (ci + 1))  # ':' plus T tokens
                        detail["ascription"] += n
                        ann += n
        i += 1
    return total, ann, detail


def main():
    d = sys.argv[1] if len(sys.argv) > 1 else "examples/ep/corpus103"
    files = sorted(
        os.path.join(d, f) for f in os.listdir(d) if f.endswith(".ep")
    )
    print(f"{'file':42} {'total':>7} {'annot':>7} {'ratio':>7}")
    t_tot = t_ann = 0
    for path in files:
        total, ann, detail = count_file(path)
        t_tot += total
        t_ann += ann
        ratio = ann / total if total else 0
        print(f"{os.path.basename(path):42} {total:7d} {ann:7d} {ratio:7.3f}")
        print(f"    detail: {detail}")
    print(f"{'TOTAL':42} {t_tot:7d} {t_ann:7d} {t_ann / t_tot if t_tot else 0:7.3f}")
    fs_path = os.path.join(d, "FAILURE_SITES.md")
    if os.path.exists(fs_path):
        with open(fs_path) as f:
            n = sum(1 for line in f if line.startswith("- ["))
        print(f"elaboration failure sites requiring human repair: {n}")


if __name__ == "__main__":
    main()
