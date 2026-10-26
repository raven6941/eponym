## Issue #402: derivation of representation specs from checked type structure.
##
## Drives `deriveSpec` at compile time over elaborated fixtures (standalone
## `.ep` surface, like `test_codegen_phase2.nim`): success cases assert the
## derived spec's shape and host type; failure cases assert the specific,
## field-naming diagnostic.

import std/[tables, macros, strutils]
import eponym_init
import eponym_embed  # elabCheckDirStateAll, HostRuntimeType
import elab          # Globals, GEntry
import eponym_mac    # hostRuntimeTypes (slice 4 differential)
import derive_repr

proc expect(ok: bool, message: string) =
  if not ok:
    quit("FAIL: " & message, 1)
  echo "ok: ", message

proc fixtureReps(checkedGlobals: Globals): Table[int, HostRuntimeType] =
  ## The hand-written base-case mappings for the fixture vocabulary:
  ## Int/Nat -> int, Vec -> vector, Wrap -> opaque WrapHost.
  result = initTable[int, HostRuntimeType]()
  for nm in ["Int", "Nat", "Vec", "Wrap"]:
    if nm in checkedGlobals and checkedGlobals[nm].tm != nil and
        checkedGlobals[nm].tm.kind == tR:
      let id = checkedGlobals[nm].tm.refId
      case nm
      of "Int", "Nat":
        result[id] = HostRuntimeType(eponymName: nm, nimType: ident"int")
      of "Vec":
        result[id] = HostRuntimeType(eponymName: nm, nimType: ident"VecHost",
                                     isRuntimeVector: true)
      of "Wrap":
        result[id] = HostRuntimeType(eponymName: nm,
                                     nimType: ident"WrapHost")

macro deriveReprSummary(src: static string, name: static string): untyped =
  ## Elaborate `src`, derive the spec for `name`, return its summary.
  let checked = elabCheckDirStateAll(src, "")
  let spec = deriveSpec(checked.globals, fixtureReps(checked.globals), name)
  result = newLit(specSummary(spec))

macro deriveReprError(src: static string, name: static string): untyped =
  ## Elaborate `src`; derivation of `name` must raise DeriveError. Returns
  ## the diagnostic message for assertion.
  let checked = elabCheckDirStateAll(src, "")
  try:
    discard deriveSpec(checked.globals, fixtureReps(checked.globals), name)
    error("deriveReprError: expected DeriveError for '" & name &
      "' but derivation succeeded")
  except DeriveError as e:
    result = newLit(e.msg)

macro registrationSummary(src: static string, name: static string): untyped =
  ## Elaborate `src`, derive the spec for `name`, register it, and return a
  ## summary of the resulting `HostRuntimeType` record for assertion.
  let checked = elabCheckDirStateAll(src, "")
  let spec = deriveSpec(checked.globals, fixtureReps(checked.globals), name)
  let m = registerDerivedMapping(spec, name)
  result = newLit(m.eponymName & "|" & $m.isRuntimeVariant & "|" &
    $m.isRuntimeVector & "|" & $m.isRuntimeOption & "|" &
    $m.nimType.toStrLit)

macro emitCodec(src: static string, name: static string,
                prefix: static string): untyped =
  ## Elaborate `src`, derive the spec for `name`, and emit the generated
  ## encoder/decoder procs into the test binary.
  let checked = elabCheckDirStateAll(src, "")
  let spec = deriveSpec(checked.globals, fixtureReps(checked.globals), name)
  let codec = genBoundaryCodec(spec, prefix)
  result = newStmtList(codec.encoder, codec.decoder)

macro emitCodecFactory(src: static string, name: static string,
                       prefix: static string): untyped =
  ## Elaborate `src`, derive the spec for `name`, and emit the generated
  ## codec-factory proc into the test binary.
  let checked = elabCheckDirStateAll(src, "")
  let spec = deriveSpec(checked.globals, fixtureReps(checked.globals), name)
  result = genCodecFactory(spec, prefix)

macro deriveOpaqueSummary(src: static string, name: static string,
                          hostType: static string): untyped =
  ## Elaborate `src`, run the slice-4 opaque kind check for `name` with the
  ## declared host type; returns "kind|typeName|nimType".
  let checked = elabCheckDirStateAll(src, "")
  let spec = deriveOpaqueSpec(checked.globals,
    fixtureReps(checked.globals), name, ident(hostType))
  result = newLit($spec.kind & "|" & spec.typeName & "|" &
    $spec.nimType.toStrLit)

macro deriveOpaqueError(src: static string, name: static string): untyped =
  ## Elaborate `src`; the slice-4 opaque check for `name` must raise
  ## DeriveError. Returns the diagnostic message for assertion.
  let checked = elabCheckDirStateAll(src, "")
  try:
    discard deriveOpaqueSpec(checked.globals, fixtureReps(checked.globals),
                             name, ident"HostT")
    error("deriveOpaqueError: expected DeriveError for '" & name &
      "' but the opaque check succeeded")
  except DeriveError as e:
    result = newLit(e.msg)

macro deriveTwoArgDifferential(src: static string): untyped =
  ## Elaborate `src`; register `runtimeDerive(Chan, PaxosChannel)` and the
  ## hand-written `runtimeType(Chan, PaxosChannel)` through
  ## `hostRuntimeTypes`. Returns "derived // manual // emitted:d/m" — the
  ## slice-4 differential property is that the two registrations are
  ## structurally identical and neither emits procs.
  let checked = elabCheckDirStateAll(src, "")
  var emittedD: seq[NimNode] = @[]
  let derived = hostRuntimeTypes(
    newStmtList(
      newCall(ident"runtimeDerive", ident"Chan", ident"PaxosChannel")),
    checked.globals, emittedD)
  var emittedM: seq[NimNode] = @[]
  let manual = hostRuntimeTypes(
    newStmtList(
      newCall(ident"runtimeType", ident"Chan", ident"PaxosChannel")),
    checked.globals, emittedM)
  proc summ(m: HostRuntimeType): string =
    m.eponymName & "|" & $m.nimType.toStrLit & "|" & $m.isRuntimeVector &
    "|" & $m.isRuntimeList & "|" & $m.isRuntimeOption & "|" &
    $m.isRuntimeVariant & "|" & $m.isRuntimeCodec & "|" &
    $m.isGenericTypeWitnessable & "|" & $m.hasRecordCodec
  result = newLit(summ(derived[0]) & " // " & summ(manual[0]) &
    " // emitted:" & $emittedD.len & "/" & $emittedM.len)

macro codecGenError(src: static string, name: static string,
                    prefix: static string): untyped =
  ## Codec generation for `name` must raise DeriveError. Returns the
  ## diagnostic for assertion.
  let checked = elabCheckDirStateAll(src, "")
  let spec = deriveSpec(checked.globals, fixtureReps(checked.globals), name)
  try:
    discard genBoundaryCodec(spec, prefix)
    error("codecGenError: expected DeriveError for '" & name &
      "' but codec generation succeeded")
  except DeriveError as e:
    result = newLit(e.msg)

macro kindDepError(): untyped =
  ## A sigma whose component kind depends on the bound value, built
  ## directly as a Term: Sig (p : Sig (x : Int). Int). fst p. The elaborator
  ## rejects this shape in surface position, so it is exercised at the Term
  ## level as defense-in-depth. Runs at compile time (like the other
  ## fixtures) so the Table instantiations stay compile-time-only.
  var g = initTable[string, GEntry]()
  let intId = 11
  g["Int"] = GEntry(tm: Term(kind: tR, refId: intId))
  let pId = 12
  g["P"] = GEntry(tm: Term(kind: tR, refId: pId),
                  ty: tmSi(Term(kind: tR, refId: intId), "p",
                           tmFst(vv(0))))
  var reps = initTable[int, HostRuntimeType]()
  reps[intId] = HostRuntimeType(eponymName: "Int", nimType: ident"int")
  try:
    discard deriveSpec(g, reps, "P")
    error("kindDepError: expected DeriveError but derivation succeeded")
  except DeriveError as e:
    result = newLit(e.msg)

const recordSrc = """
postulate(Int, Univ)
postulate(Nat, Univ)
postulate(Point, Sig(x: Int, Sig(y: Nat, Int)))
"""

const variantSrc = """
postulate(Int, Univ)
data(Tree, Univ) where
| leaf : Tree
| node (n : Int) (rest : Tree) : Tree
"""

const opaqueDepSrc = """
postulate(Int, Univ)
postulate(Nat, Univ)
postulate(Wrap, Pi(n: Nat, Univ))
postulate(Box, Sig(n: Nat, Wrap n))
"""

const vecDepSrc = """
postulate(Int, Univ)
postulate(Nat, Univ)
postulate(Vec, Pi(A: Univ, Pi(n: Nat, Univ)))
postulate(Pair2, Sig(n: Nat, Vec Int n))
"""

const higherOrderSrc = """
postulate(Int, Univ)
postulate(Bad, Sig(f: Pi(x: Int, Int), Int))
"""

const noMappingSrc = """
postulate(Int, Univ)
postulate(Mystery, Univ)
postulate(P, Sig(x: Int, Mystery))
"""

const indexedSrc = """
postulate(Int, Univ)
data(Nat, Univ) where
| zero : Nat
| suc (n : Nat) : Nat
data(IVec, Pi(A: Univ, Pi(n: Nat, Univ))) where
| ivnil (A : Univ) : IVec A zero
| ivcons (A : Univ) (n : Nat) (x : A) (xs : IVec A n) : IVec A (suc n)
"""

const vecSrc = """
postulate(Int, Univ)
data(Nat, Univ) where
| zero : Nat
| suc (n : Nat) : Nat
data(Vec, Pi(A: Univ, Pi(n: Nat, Univ))) where
| nil (A : Univ) : Vec A zero
| cons (A : Univ) (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
postulate(Pair2, Sig(n: Nat, Vec Int n))
"""

const opaqueFamSrc = """
postulate(Session, Univ)
postulate(Nat, Univ)
postulate(Chan, Session -> Univ)
postulate(Promise, Univ)
postulate(AcceptMsg, Nat -> Univ)
"""

const opaqueDefSrc = """
data(Nat, Univ) where
| zero : Nat
| suc (n : Nat) : Nat
postulate(f, Nat -> Nat)
"""

emitCodec(recordSrc, "Point", "point")
emitCodec(variantSrc, "Tree", "tree")
emitCodecFactory(vecSrc, "Pair2", "pair2CodecFactory")

when isMainModule:
  let recordSum = deriveReprSummary(recordSrc, "Point")
  expect("dkProduct" in recordSum, "record derives a product spec")
  expect("tuple[f0: int, f1: int, f2: int]" in recordSum,
    "record host type is the flat tuple, got: " & recordSum)
  expect(recordSum.count("dkInt") == 3, "record has three int components")

  let variantSum = deriveReprSummary(variantSrc, "Tree")
  expect("dkVariant" in variantSum, "data family derives a variant spec")
  expect("dkRecurse" in variantSum,
    "recursive constructor field is a recursive occurrence, not an expansion")
  expect("dkInt" in variantSum, "node payload carries the int field")

  let opaqueSum = deriveReprSummary(opaqueDepSrc, "Box")
  expect("dkOpaque" in opaqueSum and "WrapHost" in opaqueSum,
    "index-erased opaque family application derives (marker in dropped " &
    "position), got: " & opaqueSum)

  let vecSum = deriveReprSummary(vecDepSrc, "Pair2")
  expect("dkVector" in vecSum and "seq[int]" in vecSum,
    "vector length over a bound value derives (boundary-check obligation, " &
    "not a rejection), got: " & vecSum)

  let hoErr = deriveReprError(higherOrderSrc, "Bad")
  expect("function type with no runtime representation" in hoErr,
    "function-typed field fails specifically, got: " & hoErr)
  expect("Bad" in hoErr, "diagnostic names the declaration")

  let nmErr = deriveReprError(noMappingSrc, "P")
  expect("no runtime mapping for 'Mystery'" in nmErr,
    "unmapped leaf fails loudly, got: " & nmErr)

  let ixErr = deriveReprError(indexedSrc, "IVec")
  expect("is indexed" in ixErr and "IVec" in ixErr,
    "indexed family fails honestly, got: " & ixErr)

  let kdErr = kindDepError()
  expect("depends on a bound value" in kdErr,
    "kind-dependent component fails specifically, got: " & kdErr)

  # -- Slice 2: registration is structurally identical to the hand-written
  # declaration it replaces (the differential property).
  let pointReg = registrationSummary(recordSrc, "Point")
  expect(pointReg == "Point|false|false|false|tuple[f0: int, f1: int, f2: int]",
    "derived product registers the hand-written tuple mapping, got: " &
    pointReg)
  let treeReg = registrationSummary(variantSrc, "Tree")
  expect(treeReg.startsWith("Tree|true|false|false|") and
    "RuntimeVariant" in treeReg,
    "derived variant registers exactly what `runtimeVariant(Tree)` " &
    "produces, got: " & treeReg)
  let vecReg = registrationSummary(vecDepSrc, "Pair2")
  expect(vecReg.startsWith("Pair2|false|false|false|") and
    "tuple[f0: int, f1: seq[int]]" in vecReg,
    "dependent product registers the tuple mapping, got: " & vecReg)

  # -- Slice 2: generated boundary codecs roundtrip at runtime.
  let gPoint = elabCheckDirStateAll(recordSrc, "").globals
  let pointBack = pointDecode(pointEncode((1, 2, 3), gPoint), gPoint)
  expect(pointBack.f0 == 1 and pointBack.f1 == 2 and pointBack.f2 == 3,
    "record codec roundtrips (1, 2, 3)")

  let gTree = elabCheckDirStateAll(variantSrc, "").globals
  let leafBack = treeDecode(
    treeEncode(RuntimeVariant(constructor: "leaf", arguments: @[]), gTree),
    gTree)
  expect(leafBack.constructor == "leaf" and leafBack.arguments.len == 0,
    "variant codec roundtrips the nullary constructor")
  let leafVal = treeEncode(
    RuntimeVariant(constructor: "leaf", arguments: @[]), gTree)
  let nodeBack = treeDecode(
    treeEncode(RuntimeVariant(constructor: "node",
      arguments: @[intToValue(5), leafVal]), gTree), gTree)
  expect(nodeBack.constructor == "node" and nodeBack.arguments.len == 2 and
    valueToInt(nodeBack.arguments[0]) == 5,
    "variant codec roundtrips a payload constructor")

  # -- Slice 2: the codec factory selects the length-dependent codec and
  # enforces the O(1) boundary check.
  let gVec = elabCheckDirStateAll(vecSrc, "").globals
  let c2 = pair2CodecFactory(2)
  let vecBack = c2.dec(c2.enc((7, @[8, 9]), gVec), gVec)
  expect(vecBack.f0 == 7 and vecBack.f1 == @[8, 9],
    "codec factory roundtrips the dependent pair")
  var rejected = false
  try:
    discard c2.enc((7, @[8]), gVec)
  except ValueError:
    rejected = true
  expect(rejected, "factory codec rejects a length-mismatched host value")

  # -- Slice 2: opaque leaves have no structural codec (identity boundary).
  let opqErr = codecGenError(opaqueDepSrc, "Box", "box")
  expect("identity host representation" in opqErr,
    "opaque codec generation fails honestly, got: " & opqErr)

  # -- Slice 4: two-arg `runtimeDerive(Name, HostType)` — the kind is
  # derived from the checked structure, the host type declared.
  let chanOpaq = deriveOpaqueSummary(opaqueFamSrc, "Chan", "PaxosChannel")
  expect(chanOpaq == "dkOpaque|Chan|PaxosChannel",
    "indexed family is opaque-shaped, got: " & chanOpaq)
  let promOpaq = deriveOpaqueSummary(opaqueFamSrc, "Promise", "PaxosPromise")
  expect(promOpaq == "dkOpaque|Promise|PaxosPromise",
    "plain abstract type is opaque-shaped, got: " & promOpaq)
  let accOpaq = deriveOpaqueSummary(opaqueFamSrc, "AcceptMsg", "PaxosTicket")
  expect(accOpaq == "dkOpaque|AcceptMsg|PaxosTicket",
    "Nat-indexed family is opaque-shaped, got: " & accOpaq)
  let recOpaqErr = deriveOpaqueError(recordSrc, "Point")
  expect("one-arg runtimeDerive('Point')" in recOpaqErr,
    "record is not opaque: directed at the one-arg form, got: " & recOpaqErr)
  let varOpaqErr = deriveOpaqueError(variantSrc, "Tree")
  expect("one-arg runtimeDerive('Tree')" in varOpaqErr,
    "data family is not opaque: directed at the one-arg form, got: " &
    varOpaqErr)
  let ixFamOpaqErr = deriveOpaqueError(indexedSrc, "IVec")
  expect("has data constructors" in ixFamOpaqErr,
    "indexed data family is not opaque, got: " & ixFamOpaqErr)
  let defOpaqErr = deriveOpaqueError(opaqueDefSrc, "f")
  expect("not a plain or indexed type family" in defOpaqErr,
    "a term-level postulate is not a family, got: " & defOpaqErr)
  let missingOpaqErr = deriveOpaqueError(opaqueFamSrc, "Nope")
  expect("not declared" in missingOpaqErr,
    "undeclared name fails, got: " & missingOpaqErr)

  # -- Slice 4: the two-arg registration is structurally identical to the
  # hand-written `runtimeType` it replaces (the differential property).
  let diff = deriveTwoArgDifferential(opaqueFamSrc)
  let dparts = diff.split(" // ")
  expect(dparts.len == 3 and dparts[0] == dparts[1] and
    dparts[2] == "emitted:0/0",
    "two-arg runtimeDerive registers exactly what manual runtimeType " &
    "produces, got: " & diff)

  echo "test_derive_repr: all derivation cases passed"
