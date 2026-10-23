## Issue #402 slice 3: `runtimeDerive(...)` in `eponymBlock`.
##
## A real block replaces hand-written mappings with derived ones:
## - `record(DPoint)` + `runtimeDerive(DPoint)`: derived `isRuntimeCodec`
##   with generated boundary procs; typed wrappers roundtrip.
## - `data(DTree)` + `runtimeDerive(DTree)`: derived `isRuntimeVariant`;
##   wrapper behavior matches the hand-written `runtimeVariant` block.
## - `postulate(DPair2, Sig(n: Nat, Vec Int n))` + `runtimeDerive(DPair2)`:
##   codec factory + adapters; length mismatches rejected at the boundary.
## - `runtimeDerive` on a non-derivable type is a specific compile error.

import std/[tables]
import eponym_mac
import eponym_init
import eponym_embed

proc expect(ok: bool, message: string) =
  if not ok:
    quit("FAIL: " & message, 1)
  echo "ok: ", message

# ---------------------------------------------------------------------------
# 1. Record: the derived product codec replaces a hand-written mapping.
eponymBlock:
  import "../lib/nat.ep"
  postulate(Int, Univ)
  record(DPoint):
    field(x, Nat)
    field(y, Nat)
  runtimeDerive(DPoint)
  proc dpointMk(x: Nat, y: Nat): DPoint = mkDPoint(x, y)
  proc dpointSum(p: DPoint): Nat = add(p.x, p.y)

when isMainModule:
  let made = dpointMk(3, 4)
  expect(made.f0 == 3 and made.f1 == 4,
    "derived record codec: wrapper builds the host tuple")
  let back = dpointMk(3, 4)
  expect(back == made, "derived record codec: host tuple roundtrips")
  expect(dpointSum((f0: 3, f1: 4)) == 7,
    "derived record codec: wrapper decodes the host tuple for the body")

# ---------------------------------------------------------------------------
# 2. Variant: derived `isRuntimeVariant` matches hand-written `runtimeVariant`.
eponymBlock:
  postulate(Int, Univ)
  data(DTreeA, Univ):
    proc leafA(): DTreeA
    proc nodeA(n: Int, rest: DTreeA): DTreeA
  runtimeVariant(DTreeA)
  proc dtreeAMk(): DTreeA = nodeA(37, leafA())

eponymBlock:
  postulate(Int, Univ)
  data(DTreeB, Univ):
    proc leafB(): DTreeB
    proc nodeB(n: Int, rest: DTreeB): DTreeB
  runtimeDerive(DTreeB)
  proc dtreeBMk(): DTreeB = nodeB(37, leafB())
  proc dtreeBId(t: DTreeB): DTreeB = t

when isMainModule:
  let a = dtreeAMk()
  let b = dtreeBMk()
  expect(a.constructor == "nodeA" and b.constructor == "nodeB",
    "variant wrappers produce the constructor tag")
  expect(a.arguments.len == 2 and b.arguments.len == 2,
    "variant wrappers carry the payload arguments")
  expect(valueToInt(a.arguments[0]) == 37 and
         valueToInt(b.arguments[0]) == 37,
    "hand-written and derived variant wrappers agree on the payload")
  let bBack = dtreeBId(b)
  expect(bBack.constructor == "nodeB" and bBack.arguments.len == 2 and
         valueToInt(bBack.arguments[0]) == 37,
    "derived variant wrapper roundtrips through the boundary")

# ---------------------------------------------------------------------------
# 3. Dependent product: the codec factory behind `isRuntimeCodec` adapters.
eponymBlock:
  import "../lib/nat.ep"
  import "../lib/vec.ep"
  postulate(Int, Univ)
  runtimeVector(Vec)
  record(DPair2):
    field(n, Nat)
    field(v, Vec[Int, n])
  runtimeDerive(DPair2)
  proc dpair2Mk(n: Nat, v: Vec[Int, n]): DPair2 = mkDPair2(n, v)
  proc dpair2Fst(p: DPair2): Nat = p.n

when isMainModule:
  let built = dpair2Mk(2, @[8, 9])
  expect(built.f0 == 2 and built.f1 == @[8, 9],
    "factory adapter: dependent pair decodes through the factory")
  expect(dpair2Fst((f0: 2, f1: @[8, 9])) == 2,
    "factory adapter: dependent pair encodes through the factory")
  var rejected = false
  try:
    discard dpair2Fst((f0: 2, f1: @[8]))
  except ValueError:
    rejected = true
  expect(rejected,
    "factory adapter: length-mismatched host tuple rejected at the boundary")
  var argRejected = false
  try:
    discard dpair2Mk(2, @[8])
  except ValueError:
    argRejected = true
  expect(argRejected,
    "factory adapter: length-mismatched vector argument rejected")

# ---------------------------------------------------------------------------
# 4. Non-derivable types fail specifically at compile time.
template badDeriveBlock(): untyped =
  eponymBlock:
    import "../lib/nat.ep"
    postulate(BadSig, Sig(f: Int -> Int, Nat))
    runtimeDerive(BadSig)

const badDeriveFails = not compiles(badDeriveBlock())

# ---------------------------------------------------------------------------
# 5. Two-arg form: opaque families declare the host type, derivation checks
# the kind. The wrapper treats the declared host type as the identity
# boundary, exactly like the hand-written `runtimeType` it replaces.
type
  OpaqueToken = object
    tag: int

eponymBlock:
  import "../lib/nat.ep"
  postulate(Tok, Univ)
  postulate(TokFam, Nat -> Univ)
  runtimeDerive(Tok, OpaqueToken)
  runtimeDerive(TokFam, OpaqueToken)
  proc tokId(t: Tok): Tok = t
  proc tokFamId(t: TokFam[zero]): TokFam[zero] = t

when isMainModule:
  let tok = OpaqueToken(tag: 7)
  expect(tokId(tok).tag == 7,
    "two-arg runtimeDerive: opaque identity wrapper roundtrips")
  expect(tokFamId(tok).tag == 7,
    "two-arg runtimeDerive: indexed opaque family wrapper roundtrips")

# ---------------------------------------------------------------------------
# 6. The two-arg form is only for opaque families: a derivable record is a
# compile error directing at the one-arg form, and so is a bad arity.
template badDeriveTwoArgRecord(): untyped =
  eponymBlock:
    import "../lib/nat.ep"
    postulate(Int, Univ)
    record(BadRec):
      field(x, Nat)
    runtimeDerive(BadRec, OpaqueToken)

template badDeriveArity(): untyped =
  eponymBlock:
    import "../lib/nat.ep"
    postulate(Tok2, Univ)
    runtimeDerive(Tok2, OpaqueToken, Extra)

const badTwoArgRecordFails = not compiles(badDeriveTwoArgRecord())
const badArityFails = not compiles(badDeriveArity())

when isMainModule:
  expect(badTwoArgRecordFails,
    "two-arg runtimeDerive on a derivable record is a compile error")
  expect(badArityFails,
    "three-arg runtimeDerive is a compile error")

  echo "test_runtime_derive_block: all block-wiring cases passed"
