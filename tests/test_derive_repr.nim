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
postulate Int : Type 0
postulate Nat : Type 0
postulate Point : Sig (x : Int). Sig (y : Nat). Int
"""

const variantSrc = """
postulate Int : Type 0
data Tree : Type 0 where
| leaf : Tree
| node (n : Int) (rest : Tree) : Tree
"""

const opaqueDepSrc = """
postulate Int : Type 0
postulate Nat : Type 0
postulate Wrap : Pi (n : Nat). Type 0
postulate Box : Sig (n : Nat). Wrap n
"""

const vecDepSrc = """
postulate Int : Type 0
postulate Nat : Type 0
postulate Vec : Pi (A : Type 0). Pi (n : Nat). Type 0
postulate Pair2 : Sig (n : Nat). Vec Int n
"""

const higherOrderSrc = """
postulate Int : Type 0
postulate Bad : Sig (f : Pi (x : Int). Int). Int
"""

const noMappingSrc = """
postulate Int : Type 0
postulate Mystery : Type 0
postulate P : Sig (x : Int). Mystery
"""

const indexedSrc = """
postulate Int : Type 0
data Nat : Type 0 where
| zero : Nat
| suc (n : Nat) : Nat
data IVec : Pi (A : Type 0). Pi (n : Nat). Type 0 where
| ivnil (A : Type 0) : IVec A zero
| ivcons (A : Type 0) (n : Nat) (x : A) (xs : IVec A n) : IVec A (suc n)
"""

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

  echo "test_derive_repr: all derivation cases passed"
