# mac_surf.nim — front end (b): surface syntax shaped by Nim's own grammar.
#
# A macro `ettDefs` takes a block of `proc` definitions and produces a
# seq[SurfDef] of preterms (see preterm.nim). Mapping:
#   proc twice(A: Univ, f: A -> A, x: A): A = f(f(x))
#   - `Univ`            -> ?                 (Nim can't parse a bare `?`)
#   - `A -> B` (infix)  -> Pi (_ : A). B
#   - `lam(x, T, body)` -> lam (x : T). body
#   - `Sig(A, B)`       -> Sig (_ : A). B    (non-dependent for now)
#   - `(a, b)`          -> pair
#   - `fst p`, `snd p`  -> projections
#   - `f(x, y)`         -> application
# The block is `untyped`: it is never semantically analyzed as Nim code,
# only parsed — so `Univ`, `->` etc. need no Nim definitions.

import macros, preterm

proc locNode(n: NimNode): NimNode =
  let li = n.lineInfoObj
  newTree(nnkObjConstr, newIdentNode("Loc"),
    newTree(nnkExprColonExpr, ident"line", newLit(li.line)),
    newTree(nnkExprColonExpr, ident"col", newLit(li.column)))

proc genCall(name: string, args: varargs[NimNode]): NimNode =
  newCall(newIdentNode(name), args)

proc surfToPre(n: NimNode): NimNode =
  ## Generate code building the PreTerm denoted by surface node `n`.
  let lc = locNode(n)
  case n.kind
  of nnkIdent:
    case $n
    of "Univ": genCall("mkUniv", lc)
    of "Unit": genCall("mkUnitTy", lc)
    of "tt": genCall("mkUnitV", lc)
    of "Empty": genCall("mkEmptyTy", lc)
    else: genCall("mkVar", newLit($n), lc)
  of nnkInfix:
    if $n[0] == "->" and n.len == 3:
      genCall("mkArrow", surfToPre(n[1]), surfToPre(n[2]), lc)
    else:
      error("unsupported infix operator: " & $n[0], n)
  of nnkCall:
    let head = n[0]
    if head.kind == nnkIdent:
      case $head
      of "lam":
        if n.len != 4 or n[1].kind != nnkIdent:
          error("lam expects (binder, type, body)", n)
        genCall("mkLam", newLit($n[1]), surfToPre(n[2]), surfToPre(n[3]), lc)
      of "Sig":
        if n.len == 3:
          genCall("mkSigma", newLit("_"), surfToPre(n[1]), surfToPre(n[2]), lc)
        elif n.len == 4 and n[1].kind == nnkIdent:
          genCall("mkSigma", newLit($n[1]), surfToPre(n[2]), surfToPre(n[3]), lc)
        else:
          error("Sig expects (dom, cod) or (binder, dom, cod)", n)
      of "fst":
        if n.len != 2: error("fst expects one argument", n)
        genCall("mkFst", surfToPre(n[1]), lc)
      of "snd":
        if n.len != 2: error("snd expects one argument", n)
        genCall("mkSnd", surfToPre(n[1]), lc)
      else:
        var r = surfToPre(head)
        for i in 1 ..< n.len:
          r = genCall("mkApp", r, surfToPre(n[i]), lc)
        r
    else:
      error("unsupported call head", n)
  of nnkTupleConstr:
    if n.len != 2: error("only pairs (a, b) supported", n)
    genCall("mkPair", surfToPre(n[0]), surfToPre(n[1]), lc)
  of nnkPar:
    surfToPre(n[0])
  of nnkStmtList:
    if n.len == 1: surfToPre(n[0])
    else: error("expected a single expression", n)
  else:
    error("unsupported surface syntax: " & $n.kind, n)

proc procToDef(p: NimNode): NimNode =
  ## Generate code building a SurfDef from an nnkProcDef.
  var nameNode = p[0]
  if nameNode.kind == nnkPostfix: nameNode = nameNode[1]
  if nameNode.kind == nnkAccQuoted: nameNode = nameNode[0]
  let fname = $nameNode
  let lc = locNode(p)
  let params = p[3]
  if params.kind != nnkFormalParams:
    error("malformed proc", p)
  let retTy = surfToPre(params[0])
  var tele = newTree(nnkBracket)
  for i in 1 ..< params.len:
    let id = params[i]
    if id.kind != nnkIdentDefs or id.len < 3:
      error("malformed parameter", id)
    let ty = surfToPre(id[id.len - 2])
    for j in 0 ..< id.len - 2:
      if id[j].kind != nnkIdent:
        error("parameter names must be identifiers", id[j])
      tele.add newTree(nnkTupleConstr,
        newTree(nnkExprColonExpr, ident"name", newLit($id[j])),
        newTree(nnkExprColonExpr, ident"ty", ty),
        newTree(nnkExprColonExpr, ident"impl", newLit(false)),
        newTree(nnkExprColonExpr, ident"erased", newLit(false)))
  let bodyNode = surfToPre(p[6])
  newTree(nnkObjConstr, newIdentNode("SurfDef"),
    newTree(nnkExprColonExpr, ident"name", newLit(fname)),
    newTree(nnkExprColonExpr, ident"tele",
      newTree(nnkPrefix, ident"@", tele)),
    newTree(nnkExprColonExpr, ident"retTy", retTy),
    newTree(nnkExprColonExpr, ident"body", bodyNode),
    newTree(nnkExprColonExpr, ident"loc", lc))

macro ettDefs*(body: untyped): untyped =
  ## Map a block of proc definitions to a seq[SurfDef] of preterms.
  result = newTree(nnkBracket)
  for st in body:
    if st.kind != nnkProcDef:
      error("ettDefs expects proc definitions", st)
    result.add procToDef(st)
  result = newTree(nnkPrefix, ident"@", result)

# --- tests ------------------------------------------------------------

when isMainModule:
  import parse_surf

  let mDefs = ettDefs:
    proc twice(A: Univ, f: A -> A, x: A): A = f(f(x))
    proc constFn(A: Univ, B: Univ, x: A, y: B): A = x
    proc pairSwap(A: Univ, B: Univ, p: Sig(u, A, B)): Sig(v, B, A) =
      (snd(p), fst(p))

  let sDefs = parseProgram("""
proc twice (A : ?) (f : A -> A) (x : A) : A =
  f (f x)
proc constFn (A : ?) (B : ?) (x : A) (y : B) : A =
  x
proc pairSwap (A : ?) (B : ?) (p : Sig (u : A). B) : Sig (v : B). A =
  (snd p, fst p)
""")

  assert mDefs.len == 3 and sDefs.len == 3
  for i in 0 ..< 3:
    assert sDefs[i].kind == dkDef
    assert mDefs[i].name == sDefs[i].def.name
    # same preterm AST from both front ends (locations ignored by ==)
    assert mDefs[i].desugarTy() == sDefs[i].def.desugarTy(), "type mismatch: " & mDefs[i].name
    assert mDefs[i].desugarTm() == sDefs[i].def.desugarTm(), "term mismatch: " & mDefs[i].name

  # locations survive from the Nim AST
  assert mDefs[0].loc.line > 0
  assert mDefs[0].body.loc.line > 0

  # explicit lambda via lam(x, T, body)
  let lamDef = ettDefs:
    proc applyTwice(A: Univ, f: A -> A): A -> A =
      lam(x, A, f(f(x)))
  assert $lamDef[0].desugarTm() ==
    "lam (A : ?). lam (f : A -> A). lam (x : A). f (f x)"

  echo "mac_surf: all tests passed"
