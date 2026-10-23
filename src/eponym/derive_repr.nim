## Issue #402: derive representation mappings and codecs from checked type
## structure at compile time.
##
## Hand-declared mappings (`runtimeType`, `runtimeVector`, `runtimeCodec`,
## `runtimeVariant`, record codecs) are the base cases — Scala 3's hand-written
## `given`s. This module is the Mirror: a macro-time traversal of the checked
## type `Term` that synthesizes a `DerivedSpec` for products (records/Sigma),
## sums (`data` families), and leaves with existing mappings, from the specs
## of their parts. Derivation fails loudly, naming the field and the reason,
## when no honest host representation exists:
##
## - a leaf type with no declared mapping (`no runtime mapping for 'X'`),
## - a field that is a type or a function (`... is a type/function with no
##   runtime representation`),
## - an indexed family whose constructors refine an index
##   (`family 'V' is indexed ...`),
## - a component whose representation *kind* depends on a bound value
##   (`depends on the value of field 'fN' ...; no constant host layout`).
##
## Quantity-0 binders are erased from the host layout, consistent with the
## erasure pass. A vector length index that mentions a bound value does NOT
## fail derivation: the host layout (`seq[int]`) is constant and the index
## becomes a boundary-check obligation recorded on the spec (`indexTerm`)
## for the later codec-generation step — the Vec O(1) entry check is the
## existing example. The derived spec is the input to a later step
## (registration as a `HostRuntimeType` with generated boundary codecs);
## this module derives the structure and the host-type AST.

import std/[tables, macros, strutils, sequtils]
import eponym_init   # Term, TermKind, subst, Quantity
import preterm       # q0
import elab          # Globals, GEntry
import eponym_embed  # HostRuntimeType

type
  DeriveError* = object of CatchableError
    ## A specific, named derivation failure. The message always names the
    ## declaration/field and the reason — never a silent fallback.

  DerivedKind* = enum
    dkInt       # int-fragment atom (existing plain `runtimeType .. int`)
    dkNat       # canonical Nat (zero/suc): host int, `natToValue`/`valueToNat`
    dkBool      # canonical Bool (true/false): host bool, `boolToValue`/`valueToBool`
    dkOpaque    # concrete `runtimeType` identity over its declared host type
    dkVector    # existing `runtimeVector`/`runtimeList` mapping: `seq[int]`
    dkOption    # existing `runtimeOption` mapping: `Option[int]`
    dkProduct   # derived host tuple (records / Sigma)
    dkVariant   # derived tagged sum (`data` family)
    dkRecurse   # a recursive occurrence of the enclosing family

  DerivedField* = object
    ## One product component or one variant constructor payload.
    name*: string
    spec*: DerivedSpec

  DerivedSpec* = ref object
    kind*: DerivedKind
    nimType*: NimNode  # host type AST (`tuple[...]`, `int`, declared type…)
    refId*: int        # eponym type/family refId (-1 for synthesized tuples)
    typeName*: string  # eponym name, for diagnostics
    fields*: seq[DerivedField]  # product components / variant ctors
    indexTerm*: Term    # dkVector: the length index term (boundary-check
                       # obligation for the later codec step; may mention
                       # the sigma-marker when the length is a bound value)
    markerFields*: Table[int, int]  # slice 3: binder-marker refId ->
                       # product field index holding that binder's value.
                       # The Sigma walk uses one marker refId per binder
                       # depth (`deriveMarkerRefId - depth`), so a vector
                       # length mentioning a bound index attributes to the
                       # field that carries the index at runtime.

const deriveMarkerRefId* = -402
  ## Base marker refId for a Sigma-bound variable opened during derivation
  ## (mirrors codegen's `-401` marker). Each binder depth gets its own
  ## marker (`deriveMarkerRefId - depth`) so an index mentioning a bound
  ## value attributes to the field carrying it (`markerFields`).
  ## `subst` leaves `tR` nodes alone, so markers are never shifted away.

proc isDeriveMarker*(refId: int): bool =
  ## Any binder-marker refId introduced by the derivation walks.
  refId <= deriveMarkerRefId

proc deriveErr(msg: string): ref DeriveError =
  newException(DeriveError, msg)

proc kindDependsOnMarker(ty: Term): bool =
  ## Would selecting the representation *kind* for this type need the
  ## marker-bound value? True when the type head is the bound value itself
  ## (or projects/applies it): then no constant host layout exists.
  if ty.isNil: return false
  case ty.kind
  of tR: isDeriveMarker(ty.refId)
  of tFst, tSnd, tAbsurd: kindDependsOnMarker(ty.sub)
  of tApp: kindDependsOnMarker(ty.fn)
  else: false

proc headId(ty: Term): int =
  ## The head refId of a (possibly applied) type, or -1.
  var h = ty
  while not h.isNil and h.kind == tApp: h = h.fn
  if not h.isNil and h.kind == tR: h.refId else: -1

proc appArgs(ty: Term): seq[Term] =
  var h = ty
  var rev: seq[Term] = @[]
  while not h.isNil and h.kind == tApp:
    rev.add(h.arg)
    h = h.fn
  for i in countdown(rev.high, 0): result.add(rev[i])

proc isPlainIntMapping(m: HostRuntimeType): bool =
  ## Mirror of codegen's classifier: a plain `runtimeType .. -> int`.
  not m.isRuntimeVector and not m.isRuntimeList and
    not m.isRuntimeOption and not m.isRuntimeVariant and
    not m.isRuntimeCodec and not m.hasRecordCodec and
    m.nimType.kind in {nnkIdent, nnkSym} and $m.nimType == "int"

proc isOpaqueIdentityMapping(m: HostRuntimeType): bool =
  ## Mirror of codegen's classifier: a concrete `runtimeType` used as-is.
  not m.isRuntimeVector and not m.isRuntimeList and
    not m.isRuntimeOption and not m.isRuntimeVariant and
    not m.isRuntimeCodec and not m.isPlainIntMapping and
    not m.hasRecordCodec and
    not (m.nimType.kind in {nnkIdent, nnkSym} and $m.nimType == m.eponymName)

type
  DeriveCtx = object
    globals: Globals
    reps: Table[int, HostRuntimeType]
    idToName: Table[int, string]
    stack: seq[int]  # families currently being derived: a re-entrant
                     # reference is a recursive occurrence (dkRecurse),
                     # which also guards against infinite regress

proc nameOf(ctx: DeriveCtx, refId: int): string =
  if refId in ctx.idToName: ctx.idToName[refId]
  else: "refId=" & $refId

proc familyConstructors(ctx: DeriveCtx, refId: int): seq[(string, GEntry)]
  # forward (used by primitiveSpec)

proc isCanonicalNat(ctx: DeriveCtx, refId: int): bool =
  ## `refId` is the Nat family with canonical `zero`/`suc` constructors
  ## (mirrors `canonicalNatConstructorIds` in eponym_embed): its values
  ## cross the boundary via `natToValue`/`valueToNat`, not the primitive
  ## Int converters.
  if "zero" notin ctx.globals or "suc" notin ctx.globals: return false
  let z = ctx.globals["zero"]
  let s = ctx.globals["suc"]
  z.isDataConstructor and s.isDataConstructor and
    not z.ty.isNil and z.ty.kind == tR and z.ty.refId == refId and
    not s.ty.isNil and s.ty.kind == tPi and
    not s.ty.dom.isNil and s.ty.dom.kind == tR and
    s.ty.dom.refId == refId and
    not s.ty.scope.bdy.isNil and s.ty.scope.bdy.kind == tR and
    s.ty.scope.bdy.refId == refId

proc isCanonicalBool(ctx: DeriveCtx, refId: int): bool =
  ## `refId` is the Bool family with canonical nullary `true`/`false`
  ## constructors: its values cross via `boolToValue`/`valueToBool`.
  for cname in ["true", "false"]:
    if cname notin ctx.globals: return false
    let c = ctx.globals[cname]
    if not c.isDataConstructor or c.ty.isNil or
        c.ty.kind != tR or c.ty.refId != refId:
      return false
  true

proc primitiveSpec(ctx: DeriveCtx, refId: int): DerivedSpec =
  ## The int-fragment primitive base cases (mirroring the wrapper layer's
  ## `simpleRuntimeCodec`): primitive `Int`, canonical `Nat`, canonical
  ## `Bool`. Returns nil when `refId` is none of these. Manual mappings
  ## take precedence — this only fires for otherwise-unmapped leaves.
  let nm = ctx.nameOf(refId)
  if nm == "Int" and ctx.familyConstructors(refId).len == 0:
    return DerivedSpec(kind: dkInt, nimType: ident"int", refId: refId,
                       typeName: nm)
  if isCanonicalNat(ctx, refId):
    return DerivedSpec(kind: dkNat, nimType: ident"int", refId: refId,
                       typeName: nm)
  if isCanonicalBool(ctx, refId):
    return DerivedSpec(kind: dkBool, nimType: ident"bool", refId: refId,
                       typeName: nm)
  nil

proc markerFieldIndex*(spec: DerivedSpec, indexTerm: Term): int =
  ## The product field index holding the runtime value a binder-marker
  ## `indexTerm` refers to, or -1 when the term is not a field-attributed
  ## marker (a literal, a missing index, or an erased binder's marker).
  if indexTerm.isNil or indexTerm.kind != tR: return -1
  if not isDeriveMarker(indexTerm.refId): return -1
  spec.markerFields.getOrDefault(indexTerm.refId, -1)

proc leafSpec(ctx: DeriveCtx, m: HostRuntimeType, refId: int): DerivedSpec =
  ## A hand-written mapping is a base case: classify it, don't re-derive.
  let nm = ctx.nameOf(refId)
  if m.isPlainIntMapping:
    # A hand-declared `int` mapping over canonical Nat/Bool still needs
    # the Nat/Bool value converters, not the primitive Int ones.
    let prim = ctx.primitiveSpec(refId)
    if not prim.isNil: return prim
    return DerivedSpec(kind: dkInt, nimType: ident"int", refId: refId,
                       typeName: nm)
  if m.isRuntimeVector or m.isRuntimeList:
    return DerivedSpec(kind: dkVector,
      nimType: nnkBracketExpr.newTree(ident"seq", ident"int"),
      refId: refId, typeName: nm)
  if m.isRuntimeOption:
    return DerivedSpec(kind: dkOption,
      nimType: nnkBracketExpr.newTree(ident"Option", ident"int"),
      refId: refId, typeName: nm)
  if m.isOpaqueIdentityMapping:
    return DerivedSpec(kind: dkOpaque, nimType: copyNimTree(m.nimType),
                       refId: refId, typeName: nm)
  raise deriveErr("mapping for '" & nm &
    "' is a variant/codec/record mapping: derivation of composite mappings " &
    "is not supported yet; declare the composite mapping by hand")

proc deriveType(ctx: DeriveCtx, ty: Term, path: seq[string]): DerivedSpec
  # forward

proc deriveRecordProduct(ctx: DeriveCtx, name: string,
    mkEntry: GEntry, path: seq[string]): DerivedSpec =
  ## A `record` declaration elaborates to a type former (its `ty` is `Univ`);
  ## the product structure is recovered from the generated `mk<name>`
  ## constructor's Pi type, whose domains are the positional fields.
  let at = path.join(" > ")
  var fields: seq[DerivedField] = @[]
  var markerFields = initTable[int, int]()
  var cty = mkEntry.ty
  var pos = 0
  var depth = 0
  while not cty.isNil and cty.kind == tPi:
    let marker = Term(kind: tR, refId: deriveMarkerRefId - depth)
    if cty.qty != q0:
      let fname = "f" & $pos
      let dom = cty.dom
      if not dom.isNil and dom.kind == tPi:
        raise deriveErr("record field '" & fname & "' of '" & name &
          "' is a function type with no runtime representation")
      if not dom.isNil and dom.kind == tType:
        raise deriveErr("record field '" & fname & "' of '" & name &
          "' is a type with no runtime representation")
      if kindDependsOnMarker(dom):
        raise deriveErr("record field '" & fname & "' of '" & name &
          "' depends on the value of an earlier field to select its " &
          "representation; no constant host layout exists")
      fields.add(DerivedField(name: fname,
        spec: ctx.deriveType(dom, path & @[fname])))
      markerFields[marker.refId] = pos
      inc pos
    cty = subst(cty.scope.bdy, 0, marker)
    inc depth
  var tup = nnkTupleTy.newTree()
  for f in fields:
    tup.add(nnkIdentDefs.newTree(ident(f.name), f.spec.nimType,
                                newEmptyNode()))
  DerivedSpec(kind: dkProduct, nimType: tup, refId: -1, typeName: at,
             fields: fields, markerFields: markerFields)

proc familyConstructors(ctx: DeriveCtx, refId: int): seq[(string, GEntry)] =
  ## The `data` constructors whose return type head is the family refId.
  for cname, centry in ctx.globals.pairs:
    if not centry.isDataConstructor or centry.ty.isNil: continue
    var retTy = centry.ty
    while not retTy.isNil and retTy.kind == tPi: retTy = retTy.scope.bdy
    if not retTy.isNil and headId(retTy) == refId:
      result.add((cname, centry))

proc deriveFamily(ctx: DeriveCtx, refId: int,
                  path: seq[string]): DerivedSpec =
  ## Derive for an unmapped family head: a `data` family becomes a variant.
  let nm = ctx.nameOf(refId)
  var c = ctx
  c.stack.add(refId)
  let ctors = c.familyConstructors(refId)
  if ctors.len == 0:
    raise deriveErr("no runtime mapping for '" & nm &
      "' (at " & path.join(" > ") &
      "); declare `runtimeType`/`runtimeVector`/`runtimeOption` for it, " &
      "or derive one first")
  var varFields: seq[DerivedField] = @[]
  for (cname, centry) in ctors:
    # Indexed families (a constructor refines an index rather than
    # repeating a parameter) have index-dependent layout: reject honestly.
    var retTy = centry.ty
    while not retTy.isNil and retTy.kind == tPi: retTy = retTy.scope.bdy
    for a in appArgs(retTy):
      if a.kind != tV:
        raise deriveErr("family '" & nm &
          "' is indexed (constructor '" & cname &
          "' refines an index); no constant host layout exists — " &
          "declare the mapping by hand")
    var payload: seq[DerivedField] = @[]
    var cty = centry.ty
    var i = 0
    var depth = 0
    while not cty.isNil and cty.kind == tPi:
      let dom = cty.dom
      if cty.qty != q0:
        let fname = cname & "_arg" & $i
        if not dom.isNil and dom.kind == tPi:
          raise deriveErr("constructor field '" & fname & "' of '" & cname &
            "' is a function type with no runtime representation")
        if not dom.isNil and dom.kind == tType:
          raise deriveErr("constructor field '" & fname & "' of '" & cname &
            "' is a type with no runtime representation")
        if kindDependsOnMarker(dom):
          raise deriveErr("constructor field '" & fname & "' of '" & cname &
            "' depends on the value of an earlier field to select its " &
            "representation; no constant host layout exists")
        payload.add(DerivedField(name: fname,
          spec: c.deriveType(dom, path & @[cname & "." & fname])))
      cty = subst(cty.scope.bdy, 0,
        Term(kind: tR, refId: deriveMarkerRefId - depth))
      inc depth
      inc i
    varFields.add(DerivedField(name: cname,
      spec: DerivedSpec(kind: dkProduct, refId: -1, typeName: cname,
                        fields: payload)))
  DerivedSpec(kind: dkVariant, refId: refId, typeName: nm, fields: varFields)

proc deriveType(ctx: DeriveCtx, ty: Term, path: seq[string]): DerivedSpec =
  ## Derive the representation spec for a checked type term. `path` names
  ## the derivation site for diagnostics (innermost last).
  if ty.isNil:
    raise deriveErr("cannot derive a representation for a nil type (at " &
      path.join(" > ") & ")")
  let at = path.join(" > ")
  if kindDependsOnMarker(ty):
    raise deriveErr("type at " & at &
      " depends on a bound value to select its representation; " &
      "no constant host layout exists")
  case ty.kind
  of tR:
    if ty.refId in ctx.stack:
      return DerivedSpec(kind: dkRecurse, refId: ty.refId,
                         typeName: ctx.nameOf(ty.refId))
    if ty.refId in ctx.reps:
      return ctx.leafSpec(ctx.reps[ty.refId], ty.refId)
    # Unmapped int-fragment primitives are base cases (no manual
    # declaration needed); anything else must be declared or derived.
    let prim = ctx.primitiveSpec(ty.refId)
    if not prim.isNil: return prim
    return ctx.deriveFamily(ty.refId, path)
  of tApp:
    let h = headId(ty)
    if h in ctx.stack:
      return DerivedSpec(kind: dkRecurse, refId: h,
                         typeName: ctx.nameOf(h))
    if h in ctx.reps:
      let m = ctx.reps[h]
      if m.isRuntimeVector or m.isRuntimeList or m.isRuntimeOption:
        let args = appArgs(ty)
        let elemSpec =
          if args.len > 0: ctx.deriveType(args[0], path & @["element"])
          else: DerivedSpec(kind: dkInt, nimType: ident"int")
        if elemSpec.kind != dkInt:
          raise deriveErr("collection element of '" & ctx.nameOf(h) &
            "' at " & at &
            " is outside the int fragment; derive a mapping for it first")
        let base = ctx.leafSpec(m, h)
        if base.kind == dkVector:
          let idxTerm = if args.len > 1: args[1] else: nil
          return DerivedSpec(kind: dkVector, nimType: base.nimType,
                             refId: h, typeName: base.typeName,
                             indexTerm: idxTerm)
        return base
      return ctx.leafSpec(m, h)
    return ctx.deriveFamily(h, path)
  of tSi:
    # A (possibly dependent) Sigma: the host tuple of the components. Each
    # codomain is opened with the bound variable replaced by the marker;
    # the marker may survive in dropped index positions (opaque families)
    # or as a recorded boundary-check obligation (vector lengths) — only
    # a marker that selects the representation *kind* is rejected, above.
    # Each binder depth gets its own marker refId (`deriveMarkerRefId -
    # depth`); `markerFields` records which product field carries each
    # binder's runtime value, for codec-factory index attribution.
    var fields: seq[DerivedField] = @[]
    var markerFields = initTable[int, int]()
    var cur = ty
    var pos = 0
    var depth = 0
    while not cur.isNil and cur.kind == tSi:
      let marker = Term(kind: tR, refId: deriveMarkerRefId - depth)
      if cur.qty != q0:
        let fname = "f" & $pos
        fields.add(DerivedField(name: fname,
          spec: ctx.deriveType(cur.dom, path & @[fname])))
        markerFields[marker.refId] = pos
        inc pos
      cur = subst(cur.scope.bdy, 0, marker)
      inc depth
    # `cur` is the final codomain (not a tSi), possibly mentioning markers.
    let fname = "f" & $pos
    fields.add(DerivedField(name: fname,
      spec: ctx.deriveType(cur, path & @[fname])))
    var tup = nnkTupleTy.newTree()
    for f in fields:
      tup.add(nnkIdentDefs.newTree(ident(f.name), f.spec.nimType,
                                  newEmptyNode()))
    return DerivedSpec(kind: dkProduct, nimType: tup, refId: -1,
                       typeName: at, fields: fields,
                       markerFields: markerFields)
  of tPi:
    raise deriveErr("field at " & at &
      " is a function type with no runtime representation")
  of tType:
    raise deriveErr("field at " & at &
      " is a type with no runtime representation")
  else:
    raise deriveErr("cannot derive a representation for '" & at &
      "': unsupported type shape " & $ty.kind)

proc deriveSpec*(globals: Globals, reps: Table[int, HostRuntimeType],
                name: string): DerivedSpec =
  ## Derive the representation spec for the named declaration from its
  ## checked type structure. Raises `DeriveError` with a specific,
  ## field-naming diagnostic when no honest host representation exists.
  if name notin globals:
    raise deriveErr("'" & name & "' is not declared")
  let entry = globals[name]
  if entry.tm.isNil or entry.tm.kind != tR:
    raise deriveErr("'" & name & "' is not a type/family declaration")
  var idToName = initTable[int, string]()
  for n, e in globals.pairs:
    if not e.tm.isNil and e.tm.kind == tR:
      idToName[e.tm.refId] = n
  var ctx = DeriveCtx(globals: globals, reps: reps, idToName: idToName)
  let refId = entry.tm.refId
  if refId in reps:
    return ctx.leafSpec(reps[refId], refId)
  # A `data` family (its entry type is a universe, or a Pi over its
  # parameters/indices): derive the variant from its constructors.
  if ctx.familyConstructors(refId).len > 0:
    return ctx.deriveFamily(refId, @[name])
  # A `record` declaration elaborates to a type former (`ty` is `Univ`);
  # recover the product from the generated `mk<name>` constructor's Pi.
  let mkName = "mk" & name
  if mkName in globals:
    let mkEntry = globals[mkName]
    if not mkEntry.ty.isNil and mkEntry.ty.kind == tPi:
      var retTy = mkEntry.ty
      while not retTy.isNil and retTy.kind == tPi:
        retTy = retTy.scope.bdy
      if not retTy.isNil and headId(retTy) == refId:
        return ctx.deriveRecordProduct(name, mkEntry, @[name])
  # Otherwise the entry's type is the type to derive from (records/Sigma).
  return ctx.deriveType(entry.ty, @[name])

proc specSummary*(spec: DerivedSpec, indent = 0): string =
  ## A readable rendering of a derived spec, for tests and diagnostics.
  let pad = "  ".repeat(indent)
  result = pad & $spec.kind & " " & spec.typeName
  if not spec.nimType.isNil:
    result &= " : " & $spec.nimType.toStrLit
  for f in spec.fields:
    result &= "\n" & pad & "- " & f.name & ":\n" &
      specSummary(f.spec, indent + 2)

## ---------------------------------------------------------------------------
## Slice 2: registration + boundary-codec generation.
##
## `registerDerivedMapping` turns a DerivedSpec into the `HostRuntimeType`
## record the wrapper/codegen layers consume. The record is structurally
## identical to what the equivalent hand-written declaration (`runtimeType`,
## `runtimeVector`, `runtimeVariant`, ...) produces in `hostRuntimeTypes` —
## that equivalence is the differential property the tests assert.
##
## `genBoundaryCodec` synthesizes the encoder/decoder proc ASTs for a spec
## whose boundary conversion is structural (the int fragment: products and
## variants over ints, vectors, and nested products/variants). Opaque leaves
## have no structural codec: their boundary conversion is the identity host
## representation (the wrapper layer's typed `valueToHost`/`toHostValue`
## instantiations cover those; a later slice emits them from the spec).
##
## Vector lengths that mention a bound index become codec *factories*
## (`genCodecFactory`): `proc (idx0: int, ...): tuple[enc, dec]` — the
## decisions.org codec-factory decision (`Π (idx : I) -> Codec (T idx)`)
## with each index supplied as a host value. The O(1) length boundary check
## lives inside `seqToVecValue`/`vecValueToSeq`; the factory only selects
## the expected length. A vector length that is a static Nat literal needs
## no factory parameter: the literal is baked in.

proc registerDerivedMapping*(spec: DerivedSpec, name: string): HostRuntimeType =
  ## The `HostRuntimeType` registration for a derived spec: the mapping the
  ## hand-written declaration would have produced, computed instead of
  ## declared. Raises DeriveError for `dkRecurse` (never a top-level
  ## registration) and for option (no hand-written option shape is derivable
  ## yet — `runtimeOption` stays manual until its traversal lands).
  case spec.kind
  of dkInt, dkNat:
    HostRuntimeType(eponymName: name, nimType: ident"int")
  of dkBool:
    HostRuntimeType(eponymName: name, nimType: ident"bool")
  of dkVector:
    HostRuntimeType(eponymName: name, nimType: ident"seq",
                    isRuntimeVector: true)
  of dkOption:
    raise deriveErr("cannot register a derived mapping for option '" &
      name & "': runtimeOption stays hand-written for now")
  of dkOpaque:
    HostRuntimeType(eponymName: name, nimType: copyNimTree(spec.nimType))
  of dkProduct:
    HostRuntimeType(eponymName: name, nimType: copyNimTree(spec.nimType))
  of dkVariant:
    HostRuntimeType(eponymName: name, nimType: bindSym"RuntimeVariant",
                    isRuntimeVariant: true)
  of dkRecurse:
    raise deriveErr("cannot register a recursive occurrence of '" &
      name & "' as a top-level mapping")

type
  GeneratedCodec* = object
    ## encoder: `proc (x: hostT, g: RuntimeGlobals): RuntimeValue`;
    ## decoder: `proc (v: RuntimeValue, g: RuntimeGlobals): hostT`.
    encoder*, decoder*: NimNode

proc rvSym(): NimNode = bindSym"RuntimeValue"
proc rgSym(): NimNode = bindSym"RuntimeGlobals"

proc hostTypeOf(spec: DerivedSpec): NimNode =
  ## The host type AST a boundary codec converts at.
  case spec.kind
  of dkInt, dkNat: ident"int"
  of dkBool: ident"bool"
  of dkProduct: copyNimTree(spec.nimType)
  of dkVariant: bindSym"RuntimeVariant"
  of dkVector: nnkBracketExpr.newTree(ident"seq", ident"int")
  else:
    raise deriveErr("no host type for spec kind " & $spec.kind &
      " of '" & spec.typeName & "'")

proc encodeInto(spec: DerivedSpec, hostExpr, globalsExpr: NimNode,
                path: string,
                vecIdxs: Table[string, NimNode]): NimNode =
  ## Host expression -> `Value` expression for the spec.
  case spec.kind
  of dkInt:
    newCall(bindSym"intToValue", hostExpr)
  of dkNat:
    newCall(bindSym"natToValue", hostExpr, globalsExpr)
  of dkBool:
    newCall(bindSym"boolToValue", hostExpr, globalsExpr)
  of dkProduct:
    var acc = newCall(bindSym"unitValue")
    for i in countdown(spec.fields.high, 0):
      let f = spec.fields[i]
      let fh = newDotExpr(hostExpr, ident(f.name))
      acc = newCall(bindSym"pairValue",
        encodeInto(f.spec, fh, globalsExpr, path & "." & f.name, vecIdxs),
        acc)
    acc
  of dkVariant:
    var ctors = newNimNode(nnkBracket)
    for f in spec.fields: ctors.add(newLit(f.name))
    newCall(bindSym"runtimeVariantToValue", hostExpr, globalsExpr,
            newLit(spec.typeName), ctors)
  of dkVector:
    if path notin vecIdxs:
      raise deriveErr("vector component at " & path &
        " needs its length index; generate a codec factory instead")
    let itemEnc = newProc(
      params = @[rvSym(),
                 newIdentDefs(ident"item", ident"int", newEmptyNode()),
                 newIdentDefs(ident"gg", rgSym(), newEmptyNode())],
      body = newStmtList(newCall(bindSym"intToValue", ident"item")))
    newCall(bindSym"seqToVecValue", hostExpr, vecIdxs[path], globalsExpr,
            newLit(spec.typeName), itemEnc)
  of dkOpaque:
    raise deriveErr("opaque leaf '" & spec.typeName &
      "' has the identity host representation; no structural codec is " &
      "generated for it")
  of dkOption, dkRecurse:
    raise deriveErr("no boundary codec generated for spec kind " &
      $spec.kind & " of '" & spec.typeName & "' yet")

proc decodeInto(spec: DerivedSpec, valueExpr, globalsExpr: NimNode,
                path: string, vecIdxs: Table[string, NimNode],
                stmts: var seq[NimNode]): NimNode =
  ## Appends decode statements for `valueExpr`; returns the host expression.
  case spec.kind
  of dkInt:
    newCall(bindSym"valueToInt", valueExpr)
  of dkNat:
    newCall(bindSym"valueToNat", valueExpr, globalsExpr)
  of dkBool:
    newCall(bindSym"valueToBool", valueExpr, globalsExpr)
  of dkProduct:
    var cur = valueExpr
    var parts: seq[NimNode] = @[]
    for f in spec.fields:
      let headSym = genSym(nskLet, "vhead")
      stmts.add(newLetStmt(headSym,
        newCall(bindSym"runtimePairFirst", cur)))
      parts.add(decodeInto(f.spec, headSym, globalsExpr,
                           path & "." & f.name, vecIdxs, stmts))
      let restSym = genSym(nskLet, "vrest")
      stmts.add(newLetStmt(restSym,
        newCall(bindSym"runtimePairSecond", cur)))
      cur = restSym
    newTree(nnkTupleConstr, parts)
  of dkVariant:
    var ctors = newNimNode(nnkBracket)
    for f in spec.fields: ctors.add(newLit(f.name))
    newCall(bindSym"valueToRuntimeVariant", valueExpr, globalsExpr,
            newLit(spec.typeName), ctors)
  of dkVector:
    if path notin vecIdxs:
      raise deriveErr("vector component at " & path &
        " needs its length index; generate a codec factory instead")
    let itemDec = newProc(
      params = @[ident"int",
                 newIdentDefs(ident"item", rvSym(), newEmptyNode()),
                 newIdentDefs(ident"gg", rgSym(), newEmptyNode())],
      body = newStmtList(newCall(bindSym"valueToInt", ident"item")))
    newCall(bindSym"vecValueToSeq", valueExpr, vecIdxs[path], globalsExpr,
            newLit(spec.typeName), itemDec)
  of dkOpaque:
    raise deriveErr("opaque leaf '" & spec.typeName &
      "' has the identity host representation; no structural codec is " &
      "generated for it")
  of dkOption, dkRecurse:
    raise deriveErr("no boundary codec generated for spec kind " &
      $spec.kind & " of '" & spec.typeName & "' yet")

proc genBoundaryCodecWithVecIdxs*(spec: DerivedSpec, procPrefix: string,
    vecIdxs: Table[string, NimNode]): GeneratedCodec =
  ## `genBoundaryCodec` with an explicit vector-index table: static
  ## boundaries whose vector lengths are baked literals need no factory.
  if spec.kind notin {dkInt, dkNat, dkBool, dkProduct, dkVariant}:
    raise deriveErr("genBoundaryCodec needs a static boundary spec, got " &
      $spec.kind & " for '" & spec.typeName &
      "'; use genCodecFactory for index-dependent components")
  let hostT = hostTypeOf(spec)
  let x = ident"x"
  let g = ident"g"
  let v = ident"v"
  let encoder = newProc(ident(procPrefix & "Encode"),
    params = @[rvSym(),
               newIdentDefs(x, hostT, newEmptyNode()),
               newIdentDefs(g, rgSym(), newEmptyNode())],
    body = newStmtList(encodeInto(spec, x, g, "", vecIdxs)))
  var stmts: seq[NimNode] = @[]
  let decoded = decodeInto(spec, v, g, "", vecIdxs, stmts)
  stmts.add(decoded)
  let decoder = newProc(ident(procPrefix & "Decode"),
    params = @[hostT,
               newIdentDefs(v, rvSym(), newEmptyNode()),
               newIdentDefs(g, rgSym(), newEmptyNode())],
    body = newStmtList(stmts))
  GeneratedCodec(encoder: encoder, decoder: decoder)

proc genBoundaryCodec*(spec: DerivedSpec, procPrefix: string): GeneratedCodec =
  ## Synthesize encoder/decoder procs for a spec with a static boundary
  ## (int-fragment products and variants). Vector components carry a
  ## length-index obligation: use `genCodecFactory` for those.
  genBoundaryCodecWithVecIdxs(spec, procPrefix, initTable[string, NimNode]())

proc asClosure(p: NimNode): NimNode =
  ## Mark a generated proc `{.closure.}` so it may capture factory params.
  result = p
  result[4] = newTree(nnkPragma, ident"closure")

type
  VectorIndexParam* = object
    ## One vector component's codec-factory parameter (or baked literal),
    ## in product field order.
    path*: string      # vecIdxs key, e.g. ".f1"
    fieldPos*: int     # product field index of the vector component
    fieldName*: string # product field name, for diagnostics
    param*: NimNode    # the `idxN` ident, or nil when the length is baked
    literal*: int      # the baked Nat-literal length
    isLiteral*: bool
    indexTerm*: Term   # the vector's length index term (for attribution)

proc vectorIndexParams*(spec: DerivedSpec): seq[VectorIndexParam] =
  ## The codec-factory parameters for a product spec's vector components:
  ## one `int` parameter per length mentioning a bound index, a baked
  ## literal per static length. Anything else is a loud `DeriveError`.
  if spec.kind != dkProduct:
    raise deriveErr("vector index parameters need a product spec, got " &
      $spec.kind & " for '" & spec.typeName & "'")
  var pi = 0
  for fi, f in spec.fields:
    if f.spec.kind != dkVector: continue
    let p = "." & f.name
    let it = f.spec.indexTerm
    if it.isNil or kindDependsOnMarker(it):
      result.add(VectorIndexParam(path: p, fieldPos: fi, fieldName: f.name,
                                  param: ident("idx" & $pi), indexTerm: it))
      inc pi
    elif it.kind == tNatLit:
      result.add(VectorIndexParam(path: p, fieldPos: fi, fieldName: f.name,
                                  isLiteral: true,
                                  literal: int(it.natLitVal), indexTerm: it))
    else:
      raise deriveErr("vector field '" & f.name & "' of '" & spec.typeName &
        "' has a length index the codec factory cannot take as a host value")

proc genCodecFactory*(spec: DerivedSpec, procPrefix: string): NimNode =
  ## Synthesize `proc procPrefix(idx0: int, ...): tuple[enc, dec]` for a
  ## product with index-dependent (vector) components: the codec factory
  ## `Π (idx : I) -> Codec (T idx)`. Each vector field whose length mentions
  ## a bound value becomes one `int` factory parameter; a static Nat-literal
  ## length is baked in. Non-vector fields encode as in `genBoundaryCodec`.
  if spec.kind != dkProduct:
    raise deriveErr("genCodecFactory needs a product spec, got " &
      $spec.kind & " for '" & spec.typeName & "'")
  let vips = vectorIndexParams(spec)
  var vecIdxs = initTable[string, NimNode]()
  var params: seq[NimNode] = @[]
  for vip in vips:
    if vip.isLiteral:
      vecIdxs[vip.path] = newLit(vip.literal)
    else:
      params.add(newIdentDefs(vip.param, ident"int", newEmptyNode()))
      vecIdxs[vip.path] = vip.param
  if params.len == 0:
    raise deriveErr("no index-dependent component in '" & spec.typeName &
      "'; use genBoundaryCodec")
  let hostT = copyNimTree(spec.nimType)
  let x = ident"x"
  let g = ident"g"
  let v = ident"v"
  let encBody = newStmtList(encodeInto(spec, x, g, "", vecIdxs))
  var decStmts: seq[NimNode] = @[]
  decStmts.add(decodeInto(spec, v, g, "", vecIdxs, decStmts))
  let encTy = newTree(nnkProcTy,
    newTree(nnkFormalParams, rvSym(),
      newIdentDefs(x, hostT, newEmptyNode()),
      newIdentDefs(g, rgSym(), newEmptyNode())),
    newTree(nnkPragma, ident"closure"))
  let decTy = newTree(nnkProcTy,
    newTree(nnkFormalParams, hostT,
      newIdentDefs(v, rvSym(), newEmptyNode()),
      newIdentDefs(g, rgSym(), newEmptyNode())),
    newTree(nnkPragma, ident"closure"))
  let retTy = nnkTupleTy.newTree(
    nnkIdentDefs.newTree(ident"enc", encTy, newEmptyNode()),
    nnkIdentDefs.newTree(ident"dec", decTy, newEmptyNode()))
  let encClos = asClosure(newProc(params = @[rvSym(),
      newIdentDefs(x, hostT, newEmptyNode()),
      newIdentDefs(g, rgSym(), newEmptyNode())], body = encBody))
  let decClos = asClosure(newProc(params = @[hostT,
      newIdentDefs(v, rvSym(), newEmptyNode()),
      newIdentDefs(g, rgSym(), newEmptyNode())],
    body = newStmtList(decStmts)))
  let allParams = @[retTy] & params
  newProc(ident(procPrefix),
    params = allParams,
    body = newStmtList(newTree(nnkTupleConstr, encClos, decClos)))

proc valueComponent(valueExpr: NimNode, k: int): NimNode =
  ## The k-th component of a right-nested pair value.
  var cur = valueExpr
  for _ in 0 ..< k:
    cur = newCall(bindSym"runtimePairSecond", cur)
  newCall(bindSym"runtimePairFirst", cur)

proc genFactoryAdapters*(spec: DerivedSpec, procPrefix: string):
    tuple[factory, encoder, decoder: NimNode] =
  ## The codec factory for an index-dependent product, plus the
  ## `isRuntimeCodec`-shaped adapter procs that apply it: the encoder reads
  ## each length index from the host tuple field carrying it, the decoder
  ## reads each length index from the value's corresponding component
  ## (decoded through that field's own spec). Vector lengths must be a
  ## single bound field or a literal; computed indices are a loud
  ## `DeriveError`, not a silent tier-down.
  if spec.kind != dkProduct:
    raise deriveErr("genFactoryAdapters needs a product spec, got " &
      $spec.kind & " for '" & spec.typeName & "'")
  let vips = vectorIndexParams(spec)
  let indexed = vips.filterIt(not it.isLiteral)
  if indexed.len == 0:
    raise deriveErr("no index-dependent component in '" & spec.typeName &
      "'; use genBoundaryCodec")
  let factoryName = ident(procPrefix & "Factory")
  let factory = genCodecFactory(spec, procPrefix & "Factory")
  let hostT = copyNimTree(spec.nimType)
  let x = ident"x"
  let g = ident"g"
  let v = ident"v"
  var encIdxs: seq[NimNode] = @[]
  var decIdxs: seq[NimNode] = @[]
  for vip in indexed:
    let k = markerFieldIndex(spec, vip.indexTerm)
    if k < 0:
      raise deriveErr("vector field '" & vip.fieldName & "' of '" &
        spec.typeName & "' has a length index that is not a single " &
        "product field; codec factories for computed indices are not " &
        "supported yet")
    if spec.fields[k].spec.kind != dkInt and
        spec.fields[k].spec.kind != dkNat:
      raise deriveErr("vector field '" & vip.fieldName & "' of '" &
        spec.typeName & "' takes its length from field '" &
        spec.fields[k].name & "', which is not an int-valued index")
    encIdxs.add(newDotExpr(x, ident(spec.fields[k].name)))
    var decStmts: seq[NimNode] = @[]
    decIdxs.add(decodeInto(spec.fields[k].spec, valueComponent(v, k), g,
                           "", initTable[string, NimNode](), decStmts))
    if decStmts.len > 0:
      raise deriveErr("vector field '" & vip.fieldName & "' of '" &
        spec.typeName & "': index decoding needs statements; not supported")
  let encoder = newProc(ident(procPrefix & "Encode"),
    params = @[rvSym(),
               newIdentDefs(x, hostT, newEmptyNode()),
               newIdentDefs(g, rgSym(), newEmptyNode())],
    body = newStmtList(
      newCall(
        newDotExpr(newCall(factoryName, encIdxs), ident"enc"), x, g)))
  let decoder = newProc(ident(procPrefix & "Decode"),
    params = @[hostT,
               newIdentDefs(v, rvSym(), newEmptyNode()),
               newIdentDefs(g, rgSym(), newEmptyNode())],
    body = newStmtList(
      newCall(
        newDotExpr(newCall(factoryName, decIdxs), ident"dec"), v, g)))
  (factory: factory, encoder: encoder, decoder: decoder)

proc derivedCodecMapping*(spec: DerivedSpec, name: string,
                          encoder, decoder: NimNode): HostRuntimeType =
  ## The `isRuntimeCodec` registration for a derived product: the mapping
  ## the equivalent hand-written `runtimeCodec` produces, with
  ## macro-generated encoder/decoder procs.
  if spec.kind != dkProduct:
    raise deriveErr("derived codec mappings need a product spec, got " &
      $spec.kind & " for '" & spec.typeName & "'")
  HostRuntimeType(eponymName: name, nimType: copyNimTree(spec.nimType),
                  isRuntimeCodec: true, encoder: encoder, decoder: decoder)
