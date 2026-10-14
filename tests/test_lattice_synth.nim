## #170 step 5: the synthesis direction. The *same* checkLat rules run
## backwards — the term node starts at top and the type side saturates it.
## Outcomes are three-valued: reject (Bottom, with provenance), accept
## (fully determined output), or Stuck (partial state: holes awaiting
## information from outside elaboration).
##
## Usage: nim c -r --path:src --path:src/eponym --path:src/experimental/relational \
##   --path:src/experimental/staging tests/test_lattice_synth.nim

import minikanren
import lattice_elab
import rel_elab_dep
import options
import strutils

var fails = 0

proc checkChain(t: RTerm, n: int): bool =
  ## cons-chain of length n whose elements are all holes (rkVar leaves).
  if n == 0: return t.kind == rkAtom and t.name == "nil"
  if t.kind != rkPair or t.head.kind != rkAtom or t.head.name != "cons":
    return false
  let sp = t.tail
  if sp.kind != rkPair or sp.head.kind != rkVar: return false
  let sp2 = sp.tail
  if sp2.kind != rkPair: return false
  checkChain(sp2.head, n - 1)

proc check(name: string, cond: bool, detail = "") =
  if cond: echo "ok: ", name
  else:
    echo "FAIL: ", name, (if detail != "": " — " & detail else: "")
    inc fails

# 1. synth(Vec Nat 2): the spine is determined, the elements stay holes.
block:
  let r = synthLatTop(vecTy(natTy(), rint(2)), rnil())
  check("synth Vec Nat 2: ok", r.ok)
  check("synth Vec Nat 2: no failure", r.failure.isNone,
        if r.failure.isSome: $r.failure.get else: "")
  check("synth Vec Nat 2: cons-chain of 2 with hole elements",
        checkChain(r.output, 2), $r.output)
  check("synth Vec Nat 2: exactly the 2 element holes stuck",
        r.stuck.len == 2, $r.stuck)

# 2. synth(Vec Nat 0): fully determined — nil, nothing stuck.
block:
  let r = synthLatTop(vecTy(natTy(), rint(0)), rnil())
  check("synth Vec Nat 0: ok", r.ok)
  check("synth Vec Nat 0: output is nil", $r.output == $nilTm(), $r.output)
  check("synth Vec Nat 0: nothing stuck", r.stuck.len == 0, $r.stuck)

# 3. synth(Vec Nat ?idx): nil-vs-cons genuinely ambiguous — the ambiguity
#    stays in the state (no branching), reported as Stuck, not Bottom.
block:
  let r = synthLatTop(vecTy(natTy(), rvar(0)), rnil())
  check("synth Vec Nat ?idx: ok (no contradiction)", r.ok)
  check("synth Vec Nat ?idx: no failure", r.failure.isNone,
        if r.failure.isSome: $r.failure.get else: "")
  check("synth Vec Nat ?idx: root is a hole", r.output.kind == rkVar,
        $r.output)
  check("synth Vec Nat ?idx: stuck, not bottom", r.stuck.len == 1, $r.stuck)

# 4. synth(Nat): zero / suc-chains / literals all inhabit Nat — ambiguity
#    preserved in the state, no guessing.
block:
  let r = synthLatTop(natTy(), rnil())
  check("synth Nat: ok (no contradiction)", r.ok)
  check("synth Nat: no failure", r.failure.isNone,
        if r.failure.isSome: $r.failure.get else: "")
  check("synth Nat: stuck on the ambiguous inhabitant", r.stuck.len == 1,
        $r.stuck)

# 5. Backwards Bottom: partial term info (must be cons) meets type info
#    (Vec Nat 0 forces nil) — the contradiction is detected by the meet,
#    locally, with provenance. No search, no cut.
block:
  var st = initLatState()
  let tmId = st.freshNode("synth.root")
  discard st.meetShape(tmId, {hCons}, "test pre-constraint")
  let tyId = st.number(vecTy(natTy(), rint(0)))
  let ok = checkLat(tmId, tyId, @[], st)
  check("backwards bottom: rejects", not ok)
  check("backwards bottom: provenance recorded",
        st.failure.isSome and "hCons" in $st.failure.get,
        if st.failure.isSome: $st.failure.get else: "(no failure)")

if fails > 0:
  echo fails, " FAILURES"
  quit(1)
echo "all synthesis-direction checks pass"
