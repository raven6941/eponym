## Error-message snapshot corpus (issue #34).
##
## Each case is an ill-typed `.ep` program. The suite elaborates it, expects
## an ElabError, and checks three things:
##   1. the message carries a source location ("line L, col C: ..."),
##   2. the message leaks no elaborator internals (no raw R123/V6 refIds,
##      no `:$` application syntax, no P0 projection indices),
##   3. the message matches the blessed snapshot byte-for-byte (after
##      normalizing the repo-root path), so CI fails on message regressions.
##
## Re-bless after a deliberate message change:
##   nim c -r --hints:off --path:src --path:src/eponym tests/error_snapshots.nim -- --bless
## (run from the repo root). Review the diff before committing: a snapshot
## update is a deliberate UX decision, not a rubber stamp.
##
## Adding a case: drop a `*-neg.ep` fixture into tests/error_snapshots/cases/
## (or reference an existing one), add a row to `cases` below, run with
## `--bless`, and document the failure mode in tests/error_snapshots/README.md.
import os
import sequtils
import strutils
import elab

type Case = tuple[file: string, mode: string]

const cases: seq[Case] = @[
  # Reused negative fixtures from examples/ep (also exercised by run_examples).
  ("examples/ep/15b-session-types-neg.ep", "linearity: channel used twice"),
  ("examples/ep/15c-session-types-neg.ep", "conversion: distinct session constructors"),
  ("examples/ep/15d-session-types-neg.ep", "conversion: ended vs live channel"),
  ("examples/ep/15e-session-types-neg.ep", "linearity: channel used twice"),
  ("examples/ep/16a-paxos-wrong-order-neg.ep", "conversion: neutral mismatch (was: raw R528 leak)"),
  ("examples/ep/16b-paxos-wrong-value-neg.ep", "conversion: neutral mismatch (was: raw R5/P0 leak)"),
  ("examples/ep/17a-convex-neg.ep", "conversion: DCP constructor confusion"),
  ("examples/ep/18a-vecdim-neg.ep", "conversion: dimension mismatch (noConfusion)"),
  ("examples/ep/18b-vecdim-neg.ep", "conversion: matrix dimension mismatch"),
  ("examples/ep/18c-vecdim-neg.ep", "conversion: vector expression mismatch"),
  ("examples/ep/19b-higher-order-neg.ep", "positivity: family in higher-order domain"),
  ("examples/ep/21a-borrow-double-use-neg.ep", "linearity: borrow used twice"),
  ("examples/ep/21b-borrow-owner-use-neg.ep", "linearity: owner and borrow both used"),
  ("examples/ep/21c-borrow-drop-neg.ep", "linearity: borrow dropped"),
  ("examples/ep/24-import-missing-neg.ep", "import: missing file (path normalized)"),
  ("examples/ep/25a-clause-redundant-neg.ep", "clauses: redundant clause"),
  ("examples/ep/25c-clause-nested-overlap-neg.ep", "clauses: nested overlap"),
  ("examples/ep/25d-clause-nested-missing-neg.ep", "clauses: missing case"),
  # Dedicated fixtures for failure modes the example set did not cover.
  ("tests/error_snapshots/cases/ann-mismatch-neg.ep", "conversion: ascription mismatch names both program points"),
  ("tests/error_snapshots/cases/scope-unbound-neg.ep", "scope: unbound variable"),
  ("tests/error_snapshots/cases/arity-mismatch-neg.ep", "application: too many arguments"),
  ("tests/error_snapshots/cases/unsolved-meta-neg.ep", "metavariable: unsolved hole"),
  ("tests/error_snapshots/cases/red-mismatch-neg.ep", "red rule: unknown eliminator"),
  ("tests/error_snapshots/cases/data-bad-ctor-neg.ep", "data: constructor return not the family"),
  ("tests/error_snapshots/cases/data-reserved-family-neg.ep", "data: family named 'C' reserved for the motive"),
  ("tests/error_snapshots/cases/tactic-unknown-neg.ep", "tactic: unknown tactic name"),
  ("tests/error_snapshots/cases/tactic-assumption-fail-neg.ep", "tactic: assumption with no matching hypothesis"),
  ("tests/error_snapshots/cases/tactic-refl-noteq-neg.ep", "tactic: refl on non-equality goal"),
  ("tests/error_snapshots/cases/erased-use-neg.ep", "quantity: erased variable used"),
  ("tests/error_snapshots/cases/refl-fail-neg.ep", "tactic: refl on unequal terms"),
  ("tests/error_snapshots/cases/unit-ty-vs-int-neg.ep", "literals: unit value where an integer is expected (issue #458, single-syntax spelling)"),
]

const snapDir = "tests/error_snapshots/snapshots"

proc isWordChar(c: char): bool =
  c.isAlphaNumeric() or c == '_'

proc hasRawIndexLeak(msg: string): bool =
  ## Raw elaborator internals a user should never see: refIds / de Bruijn
  ## indices rendered as R123 or V6, the kernel `$` printer's `:$`
  ## application syntax, and raw projection indices P0. (Written without
  ## `re`: libpcre is not available in this environment.)
  if ":$" in msg: return true
  var i = 0
  while i < msg.len:
    let c = msg[i]
    if c in {'R', 'V', 'P'} and (i == 0 or not isWordChar(msg[i-1])):
      var j = i + 1
      while j < msg.len and msg[j].isDigit(): inc j
      if j > i + 1 and (j >= msg.len or not isWordChar(msg[j])):
        # 'P' needs the digit run to look like a projection index; 'R'/'V'
        # single letters followed by digits are never user syntax here.
        return true
    inc i
  false

proc hasLocation(msg: string): bool =
  ## Messages start "line L, col C: " (see elabErr).
  if not msg.startsWith("line "): return false
  let rest = msg[5 .. ^1]
  let comma = rest.find(", col ")
  if comma < 0: return false
  let after = rest[comma + 6 .. ^1]
  let colon = after.find(": ")
  if colon < 0: return false
  rest[0 ..< comma].allIt(it.isDigit()) and
    after[0 ..< colon].allIt(it.isDigit())

proc normalize(msg: string): string =
  ## Machine-dependent bits are normalized so snapshots are portable:
  ## file paths are asserted by the imported-source regression instead.
  let normalized = msg.replace(getCurrentDir(), "<root>").strip()
  if normalized.startsWith("<root>"):
    let marker = normalized.find(":line ")
    if marker >= 0: return normalized[marker + 1 .. ^1]
  normalized

proc snapPath(file: string): string =
  snapDir / file.splitFile().name & ".txt"

proc checkCase(c: Case, bless: bool): bool =
  let msg =
    try:
      discard elabCheckFile(c.file)
      echo "FAIL: ", c.file, " — elaborated cleanly, expected ElabError"
      return false
    except ElabError as e:
      normalize(e.msg)
    except CatchableError as e:
      echo "FAIL: ", c.file, " — expected ElabError, got ", e.name, ": ",
        e.msg.splitLines()[0]
      return false
  if not hasLocation(msg):
    echo "FAIL: ", c.file, " — no source location in message: ", msg.splitLines()[0]
    return false
  if hasRawIndexLeak(msg):
    echo "FAIL: ", c.file, " — internal leak in message: ", msg.splitLines()[0]
    return false
  let sp = snapPath(c.file)
  if bless:
    writeFile(sp, msg & "\n")
    echo "blessed: ", c.file
    return true
  if not fileExists(sp):
    echo "FAIL: ", c.file, " — no snapshot; run with --bless"
    return false
  let expected = readFile(sp).strip()
  if msg != expected:
    echo "FAIL: ", c.file, " — message changed:"
    echo "  expected: ", expected.splitLines()[0]
    echo "  actual:   ", msg.splitLines()[0]
    echo "  (run with --bless to accept the new message deliberately)"
    return false
  echo "ok [", c.mode, "]: ", c.file
  true

let bless = "--bless" in commandLineParams()
var failed = 0
for c in cases:
  if not checkCase(c, bless):
    inc failed
echo "--- ", cases.len - failed, "/", cases.len, " error snapshots ok ---"
if failed > 0 and not bless:
  quit(1)
