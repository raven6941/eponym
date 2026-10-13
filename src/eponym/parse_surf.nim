# parse_surf.nim — the canonical surface syntax of Eponym.
#
# This grammar is the single definition of Eponym's surface syntax
# (issue #144: Eponym is embedded-first, so there is exactly one syntax).
# Both entry points go through this parser:
#   - standalone `.ep` files: lexed and parsed here directly;
#   - embedded `eponymBlock` (eponym_mac.nim): `blockToEponym` converts the
#     Nim AST to a source string in this grammar, which is then parsed here.
# There is no second grammar to keep in sync — only a Nim-AST-to-string
# mapping, whose rules are listed below.
#
# Surface syntax (Nim-consistent):
#   program = decl*
#   decl    = proc | def | postulate | elim | red | data | import
#   import  = "import" string        -- multi-file programs (issue #49)
#   proc    = "proc" name tele ":" term "=" term
#   tele    = (binder)*
#   binder  = "(" name ":" term ")" | "{" name ":" term "}"  -- {} = implicit
#            | "(" qty name ":" term ")"  -- qty: 0 (erased), 1 (linear),
#                                            or a quantity variable (#66)
#   term    = arrow
#   arrow   = app ("->" arrow)?              -- right associative
#   app     = atom+
#   atom    = "(" term ")" | "(" term "," term ")" | "(" term ":" term ")"
#            | "lam" binder "." term | "Pi" binder "." term
#            | "Sig" binder "." term
#            | "let" name (":" term)? "=" term "in" term
#            | "fst" atom | "snd" atom | "by" tactic
#            | "_"                                     -- hole (Experiment 3)
#            | name | "?" | "1" | "<>" | "O" | integer
#   binder-arrow: "(" name ":" term ")" "->" term  -- binds name (issue #65)
# Comments: `--` or `#` to end of line.
#
# eponymBlock Nim-AST mapping (eponym_mac.nim `blockToEponym`):
#   `Univ`                -> `?`            (Nim can't parse a bare `?`)
#   `unitTy`              -> `1`            (unit type; `1` lexes as unit, #151)
#   `emptyTy`             -> `O`            (empty type, #151)
#   `unitv`               -> `<>`           (unit value; `<>` isn't valid Nim, #151)
#   `A -> B` (infix)      -> Pi (_ : A). B  (right associative)
#   `lam(x, T, body)`     -> lam (x : T). body
#   `lam(x {.linear.}, T, body)` -> lam (1 x : T). body   (quantity binders, #151)
#   `(t : T)`             -> (t : T)            (ascription, #151)
#   `let y: T = v` (in proc bodies) -> let y : T = v in ...
#   `Sig(A, B)`           -> Sig (_ : A). B
#   `Sig(x, A, B)`        -> Sig (x : A). B
#   `Pi(x: A, y: B, C)`   -> Pi (x : A). Pi (y : B). C
#   `Pi{A: T, ...}`       -> Pi {A : T}. ...        (implicit binders)
#   `ch {.linear.}`       -> (1 ch : T)             (quantity prefix)
#   `ch {.erased.}`       -> (0 ch : T)
#   `ch {.qvar(q).}`      -> (q ch : T)             (quantity *variable*, #151/#66)
#   `(a, b)`              -> pair; `fst p` / `snd p` -> projections
#   `f(x, y)`             -> application `f x y`
#   `byTac(tac)`          -> by tac                (tactic terms, #151)
#   `vecnil`              -> `nil`          (`nil` is a Nim keyword)
#   integer `1`           -> `(suc zero)`    (`1` lexes as the unit type)
#   `data(N, T):` block   -> data N : T where | ctor ...
#   `postulate(N, T)`     -> postulate N : T
#   `elim(N, T)`          -> elim N : T             (#151)
#   `red(lhs, rhs)`       -> red lhs = rhs          (#151)
#   `def(N, T):` block    -> def N : T, with `clause([pats], rhs)` -> | pats = rhs (#151)
#   `import "path"`       -> import "path"
#
# Mapping completeness (issue #151): every surface form is emittable from
# eponymBlock — the former divergences (elim/red, `by` tactics, `def`
# clause-style definitions, quantity-variable binders, the unit value `<>`)
# are all closed, and the previously unlisted unit/empty types, term
# ascriptions `(t : T)`, typed `let`, and quantity-annotated `lam` binders
# are covered too. One remainder: implicit-binder lambdas (`lam {x : T}. t`)
# have no Nim-side spelling (no surface-syntax corpus usage; `{x: T}` in
# expression position would collide with the Pi-implicit table syntax).
# If a new surface form is added to the grammar above, a mapping (or a
# documented reason it cannot be emitted) must be added here in the same
# commit.

import preterm, strutils

type
  TokKind = enum
    tkEof, tkIdent, tkInt, tkString,
    tkDef, tkClauses, tkPostulate, tkElim, tkRed, tkData, tkWhere, tkBy,
    tkImport,
    tkLam, tkPi, tkSig, tkLet, tkIn, tkFst, tkSnd,
    tkUniv, tkUnitTy, tkUnitV, tkEmptyTy,
    tkLParen, tkRParen, tkLBrace, tkRBrace,
    tkColon, tkColonEq, tkDot, tkComma, tkArrow, tkEq, tkPipe
  Token = object
    kind: TokKind
    lexeme: string
    loc: Loc
  Parser = object
    toks: seq[Token]
    pos: int
  ParseError* = object of CatchableError
    loc*: Loc

proc fail(loc: Loc, msg: string): ref ParseError =
  result = newException(ParseError, "line " & $loc.line & ", col " & $loc.col &
    ": " & msg)
  result.loc = loc

# --- lexer -----------------------------------------------------------

const keywords = [
  ("proc", tkDef), ("def", tkClauses),
  ("postulate", tkPostulate), ("elim", tkElim), ("red", tkRed),
  ("data", tkData), ("where", tkWhere), ("by", tkBy),
  ("import", tkImport),
  ("lam", tkLam), ("Pi", tkPi), ("Sig", tkSig),
  ("let", tkLet), ("in", tkIn), ("fst", tkFst), ("snd", tkSnd)]

proc isIdentStart(c: char): bool = c.isAlphaAscii or c == '_'
proc isIdentChar(c: char): bool = c.isAlphaNumeric or c in {'_', '\''}

proc lex(src: string): seq[Token] =
  var i = 0
  var line = 1
  var col = 1
  proc curLoc(): Loc = Loc(line: line, col: col)
  while i < src.len:
    let c = src[i]
    if c == '\n':
      inc line; col = 1; inc i
    elif c in {' ', '\t', '\r'}:
      inc col; inc i
    elif c == '-' and i + 1 < src.len and src[i+1] == '-':
      while i < src.len and src[i] != '\n': inc i  # -- comment
    elif c == '#':
      while i < src.len and src[i] != '\n': inc i  # # comment (Nim-style)
    elif isIdentStart(c):
      let l = curLoc()
      var j = i
      while j < src.len and isIdentChar(src[j]): inc j
      let w = src[i ..< j]
      col += j - i; i = j
      var k = tkIdent
      for (kw, kk) in keywords:
        if w == kw: k = kk; break
      if k == tkIdent:
        if w == "O": k = tkEmptyTy
      result.add Token(kind: k, lexeme: w, loc: l)
    elif c == '?':
      result.add Token(kind: tkUniv, lexeme: "?", loc: curLoc())
      inc col; inc i
    elif c == '"':
      # String literal (issue #49: `import "path"`); only `\"` escapes.
      let l = curLoc()
      inc col; inc i
      var s = ""
      while i < src.len and src[i] != '"':
        if src[i] == '\\' and i + 1 < src.len and src[i+1] == '"':
          s.add('"'); col += 2; i += 2
        elif src[i] == '\n':
          raise fail(l, "unterminated string literal")
        else:
          s.add(src[i]); inc col; inc i
      if i >= src.len: raise fail(l, "unterminated string literal")
      inc col; inc i  # closing quote
      result.add Token(kind: tkString, lexeme: s, loc: l)
    elif c in {'0'..'9'}:
      let l = curLoc()
      var j = i
      while j < src.len and src[j] in {'0'..'9'}: inc j
      let w = src[i ..< j]
      col += j - i; i = j
      if w == "1":
        # Single 1 is the unit type (backward compat, QTT); the integer
        # literal one is written 01 (issue #158: the renderer emits `01`
        # for pkInt(1) so render->parse stays faithful).
        result.add Token(kind: tkUnitTy, lexeme: "1", loc: l)
      else:
        result.add Token(kind: tkInt, lexeme: w, loc: l)
    elif c == '<' and i + 1 < src.len and src[i+1] == '>':
      result.add Token(kind: tkUnitV, lexeme: "<>", loc: curLoc())
      col += 2; i += 2
    elif c == '(':
      result.add Token(kind: tkLParen, lexeme: "(", loc: curLoc())
      inc col; inc i
    elif c == ')':
      result.add Token(kind: tkRParen, lexeme: ")", loc: curLoc())
      inc col; inc i
    elif c == '{':
      result.add Token(kind: tkLBrace, lexeme: "{", loc: curLoc())
      inc col; inc i
    elif c == '}':
      result.add Token(kind: tkRBrace, lexeme: "}", loc: curLoc())
      inc col; inc i
    elif c == ',':
      result.add Token(kind: tkComma, lexeme: ",", loc: curLoc())
      inc col; inc i
    elif c == '.':
      result.add Token(kind: tkDot, lexeme: ".", loc: curLoc())
      inc col; inc i
    elif c == '=':
      result.add Token(kind: tkEq, lexeme: "=", loc: curLoc())
      inc col; inc i
    elif c == '|':
      result.add Token(kind: tkPipe, lexeme: "|", loc: curLoc())
      inc col; inc i
    elif c == ':':
      let l = curLoc()
      if i + 1 < src.len and src[i+1] == '=':
        result.add Token(kind: tkColonEq, lexeme: ":=", loc: l)
        col += 2; i += 2
      else:
        result.add Token(kind: tkColon, lexeme: ":", loc: l)
        inc col; inc i
    elif c == '-' and i + 1 < src.len and src[i+1] == '>':
      result.add Token(kind: tkArrow, lexeme: "->", loc: curLoc())
      col += 2; i += 2
    else:
      raise fail(curLoc(), "unexpected character '" & c & "'")
  result.add Token(kind: tkEof, lexeme: "", loc: curLoc())

# --- parser ----------------------------------------------------------

proc peek(p: Parser): Token = p.toks[p.pos]
proc next(p: var Parser): Token =
  result = p.toks[p.pos]
  if p.pos < p.toks.high: inc p.pos

proc expect(p: var Parser, k: TokKind, what: string): Token =
  result = p.next()
  if result.kind != k:
    raise fail(result.loc, "expected " & what & ", got '" & result.lexeme & "'")

proc isAtomStart(k: TokKind): bool =
  k in {tkIdent, tkInt, tkUniv, tkUnitTy, tkUnitV, tkEmptyTy, tkLParen,
        tkLam, tkPi, tkSig, tkFst, tkSnd, tkBy}

proc parseTerm(p: var Parser): PreTerm  # forward

proc parseBinder(p: var Parser): tuple[name: string, ty: PreTerm, impl: bool, erased: bool, qty: Qty] =
  ## "(" name ":" term ")" | "{" name ":" term "}"  (braces = implicit)
  ## "(0" name ":" term ")"  (0 = erased, Experiment 9)
  ## "(1" name ":" term ")"  (1 = linear, Issue #64)
  ## "(q" name ":" term ")"  (q = quantity variable, Issue #66)
  let t = p.next()
  let impl = t.kind == tkLBrace
  if not impl and t.kind != tkLParen:
    raise fail(t.loc, "expected '(' or '{', got '" & t.lexeme & "'")
  var erased = false
  var qty: Qty = qOmega
  # Note: "1" lexes as tkUnitTy (unit type), not tkInt; "0" lexes as tkInt.
  # Accept both for quantity annotations.
  let pk = p.peek()
  if not impl and (pk.kind == tkInt or (pk.kind == tkUnitTy and pk.lexeme == "1")):
    let qlex = pk.lexeme
    if qlex == "0":
      discard p.next()  # consume the 0
      erased = true
      qty = q0
    elif qlex == "1":
      discard p.next()  # consume the 1
      qty = q1
    # else: not a quantity, leave it (will fail as binder name)
  elif not impl and pk.kind == tkIdent and p.pos + 1 <= p.toks.high and
       p.toks[p.pos + 1].kind == tkIdent:
    # Quantity variable: an identifier followed by another identifier (the
    # binder name), e.g. `(q x : A)`. `(q : A)` still parses `q` as the name.
    qty = qtyVar(pk.lexeme)
    discard p.next()  # consume the quantity variable name
  let xn = p.expect(tkIdent, "binder name")
  discard p.expect(tkColon, "':'")
  let ty = p.parseTerm()
  if impl: discard p.expect(tkRBrace, "'}'")
  else: discard p.expect(tkRParen, "')'")
  (xn.lexeme, ty, impl, erased, qty)

proc parseAtom(p: var Parser): PreTerm =
  let t = p.next()
  case t.kind
  of tkIdent:
    if t.lexeme == "_": mkHole(t.loc)  # hole (Experiment 3)
    else: mkVar(t.lexeme, t.loc)
  of tkUniv: mkUniv(t.loc)
  of tkUnitTy: mkUnitTy(t.loc)
  of tkUnitV: mkUnitV(t.loc)
  of tkEmptyTy: mkEmptyTy(t.loc)
  of tkInt: mkInt(parseInt(t.lexeme), t.loc)
  of tkBy:
    let tac = p.expect(tkIdent, "tactic name after 'by'")
    PreTerm(loc: t.loc, kind: pkBy, name: tac.lexeme)
  of tkLParen:
    let e = p.parseTerm()
    let t2 = p.next()
    case t2.kind
    of tkRParen: e
    of tkComma:
      let e2 = p.parseTerm()
      discard p.expect(tkRParen, "')'")
      mkPair(e, e2, t.loc)
    of tkColon:
      let ty = p.parseTerm()
      discard p.expect(tkRParen, "')'")
      mkAnn(e, ty, t.loc)
    else: raise fail(t2.loc, "expected ',', ':', or ')', got '" & t2.lexeme & "'")
  of tkLam:
    # lam x. body (unannotated, Experiment 3) | lam (x : T). body | lam {x : T}. body
    if p.peek().kind == tkIdent:
      let xn = p.next()
      discard p.expect(tkDot, "'.'")
      mkLam(xn.lexeme, nil, p.parseTerm(), t.loc)
    else:
      let b = p.parseBinder()
      discard p.expect(tkDot, "'.'")
      mkLam(b.name, b.ty, p.parseTerm(), t.loc, b.impl, b.erased, b.qty)
  of tkPi, tkSig:
    let b = p.parseBinder()
    if b.impl and t.kind == tkSig:
      raise fail(t.loc, "implicit Sigma binders are not supported")
    discard p.expect(tkDot, "'.'")
    let body = p.parseTerm()
    case t.kind
    of tkPi: mkPi(b.name, b.ty, body, t.loc, b.impl, b.erased, b.qty)
    else: mkSigma(b.name, b.ty, body, t.loc)
  of tkFst:
    mkFst(p.parseAtom(), t.loc)
  of tkSnd:
    mkSnd(p.parseAtom(), t.loc)
  of tkLet:
    let xn = p.expect(tkIdent, "binder name")
    var ann: PreTerm = nil
    if p.peek().kind == tkColon:
      discard p.next()
      ann = p.parseTerm()
    discard p.expect(tkEq, "'='")
    let val = p.parseTerm()
    discard p.expect(tkIn, "'in'")
    let body = p.parseTerm()
    mkLet(xn.lexeme, ann, val, body, t.loc)
  else:
    raise fail(t.loc, "expected a term, got '" & t.lexeme & "'")

proc parseApp(p: var Parser): PreTerm =
  result = p.parseAtom()
  while p.peek().kind.isAtomStart():
    let loc = result.loc
    result = mkApp(result, p.parseAtom(), loc)

proc atBinderArrow(p: Parser): bool =
  ## Issue #65: token lookahead for a binder in arrow position:
  ## `(x : A) ->`, `{x : A} ->`, `(0 x : A) ->`, `(q x : A) ->`.
  ## Mirrors parseBinder's prefix; consumes no parser state.
  var i = p.pos
  let open = p.toks[i].kind
  if open notin {tkLParen, tkLBrace}: return false
  inc i
  var needName = true
  if open == tkLParen and i <= p.toks.high:
    let q = p.toks[i]
    if q.kind == tkInt and q.lexeme in ["0", "1"]:
      inc i
    elif q.kind == tkUnitTy and q.lexeme == "1":
      inc i
    elif q.kind == tkIdent and i + 1 <= p.toks.high and
         p.toks[i + 1].kind == tkIdent:
      i += 2  # `(q x : A)`: quantity variable + binder name
      needName = false
  if needName:
    if i > p.toks.high or p.toks[i].kind != tkIdent: return false
    inc i
  if i > p.toks.high or p.toks[i].kind != tkColon: return false
  inc i
  var depth = 1  # balanced scan for the matching close bracket
  while i <= p.toks.high and depth > 0:
    case p.toks[i].kind
    of tkLParen, tkLBrace: inc depth
    of tkRParen, tkRBrace: dec depth
    else: discard
    inc i
  if depth != 0: return false
  i <= p.toks.high and p.toks[i].kind == tkArrow

proc parseTerm(p: var Parser): PreTerm =
  # Issue #65: `(x : A) -> B` binds x (a Pi); it was previously parsed as
  # an ascription, leaving x unbound in B.
  if p.atBinderArrow():
    let loc = p.peek().loc
    let b = p.parseBinder()
    discard p.expect(tkArrow, "'->'")
    return mkPi(b.name, b.ty, p.parseTerm(), loc, b.impl, b.erased, b.qty)
  let lhs = p.parseApp()
  if p.peek().kind == tkArrow:
    let t = p.next()
    mkArrow(lhs, p.parseTerm(), t.loc)
  else:
    lhs

proc parseDef(p: var Parser): SurfDef =
  let t = p.expect(tkDef, "'proc'")
  let nm = p.expect(tkIdent, "definition name")
  var tele: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool, qty: Qty]] = @[]
  while p.peek().kind in {tkLParen, tkLBrace}:
    let b = p.parseBinder()
    tele.add b
  discard p.expect(tkColon, "':'")
  let retTy = p.parseTerm()
  discard p.expect(tkEq, "'='")
  let body = p.parseTerm()
  SurfDef(name: nm.lexeme, tele: tele, retTy: retTy, body: body, loc: t.loc)

proc parsePostulate(p: var Parser): SurfDecl =
  let t = p.expect(tkPostulate, "'postulate'")
  let nm = p.expect(tkIdent, "postulate name")
  discard p.expect(tkColon, "':'")
  let ty = p.parseTerm()
  SurfDecl(kind: dkPostulate, name: nm.lexeme, ty: ty, dloc: t.loc)

proc parseElim(p: var Parser): SurfDecl =
  let t = p.expect(tkElim, "'elim'")
  let nm = p.expect(tkIdent, "eliminator name")
  discard p.expect(tkColon, "':'")
  let ty = p.parseTerm()
  SurfDecl(kind: dkElim, name: nm.lexeme, ty: ty, dloc: t.loc)

proc parseRed(p: var Parser): SurfDecl =
  let t = p.expect(tkRed, "'red'")
  let lhs = p.parseTerm()
  discard p.expect(tkEq, "'='")
  let rhs = p.parseTerm()
  SurfDecl(kind: dkRed, lhs: lhs, rhs: rhs, rloc: t.loc)

proc parseData(p: var Parser): SurfDecl =
  ## data Vec (A : ?) : Nat -> ? where
  ## | nil : Vec A zero
  ## | cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
  let t = p.expect(tkData, "'data'")
  let nm = p.expect(tkIdent, "datatype name")
  var params: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool, qty: Qty]] = @[]
  while p.peek().kind in {tkLParen, tkLBrace}:
    params.add p.parseBinder()
  discard p.expect(tkColon, "':'")
  let indexTy = p.parseTerm()
  discard p.expect(tkWhere, "'where'")
  var ctors: seq[DataCtor] = @[]
  while p.peek().kind == tkPipe:
    discard p.next()
    let cnm = p.expect(tkIdent, "constructor name")
    var tele: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool, qty: Qty]] = @[]
    while p.peek().kind in {tkLParen, tkLBrace}:
      tele.add p.parseBinder()
    discard p.expect(tkColon, "':'")
    let retTy = p.parseTerm()
    ctors.add DataCtor(name: cnm.lexeme, tele: tele, retTy: retTy,
                       cloc: cnm.loc)
  if ctors.len == 0:
    raise fail(t.loc, "data declaration needs at least one constructor")
  SurfDecl(kind: dkData, dname: nm.lexeme, params: params, indexTy: indexTy,
           ctors: ctors, daloc: t.loc)

proc parseClauses(p: var Parser): SurfDecl =
  ## `def name : Ty` followed by `| pat1 .. patn = rhs` clauses.
  ## Each pattern is an atom; constructor applications need parens: `(suc m)`.
  let t = p.expect(tkClauses, "'def'")
  let nm = p.expect(tkIdent, "definition name")
  discard p.expect(tkColon, "':'")
  let ty = p.parseTerm()
  var clauses: seq[Clause] = @[]
  while p.peek().kind == tkPipe:
    let ploc = p.next().loc
    var pats: seq[PreTerm] = @[]
    while p.peek().kind != tkEq:
      if p.peek().kind == tkEof:
        raise fail(ploc, "unterminated clause: expected '='")
      pats.add p.parseAtom()
    discard p.expect(tkEq, "'='")
    let rhs = p.parseTerm()
    if pats.len == 0:
      raise fail(ploc, "clause needs at least one pattern")
    clauses.add Clause(pats: pats, rhs: rhs, cloc: ploc)
  if clauses.len == 0:
    raise fail(t.loc, "'def' needs at least one '|'-clause")
  SurfDecl(kind: dkClauses,
           clausesDef: ClausesDef(name: nm.lexeme, ty: ty, clauses: clauses,
                                  loc: t.loc))

proc parseImport(p: var Parser): SurfDecl =
  ## Issue #49: `import "path"` — multi-file programs.
  let t = p.expect(tkImport, "'import'")
  let s = p.expect(tkString, "import path string")
  SurfDecl(kind: dkImport, ipath: s.lexeme, iloc: t.loc)

proc parseDecl(p: var Parser): SurfDecl =
  case p.peek().kind
  of tkDef: SurfDecl(kind: dkDef, def: p.parseDef())
  of tkClauses: p.parseClauses()
  of tkPostulate: p.parsePostulate()
  of tkElim: p.parseElim()
  of tkRed: p.parseRed()
  of tkData: p.parseData()
  of tkImport: p.parseImport()
  else: raise fail(p.peek().loc, "expected 'proc', 'def', 'postulate', 'elim', 'red', 'data' or 'import'")

proc parseProgram*(src: string): seq[SurfDecl] =
  ## Parse a whole program; raises ParseError with source location.
  var p = Parser(toks: lex(src), pos: 0)
  while p.peek().kind != tkEof:
    result.add p.parseDecl()

# --- tests ------------------------------------------------------------

when isMainModule:
  let prog = parseProgram("""
proc twice (A : ?) (f : A -> A) (x : A) : A =
  f (f x)

-- const and pairSwap
proc const (A : ?) (B : ?) (x : A) (y : B) : A =
  x

proc pairSwap (A : ?) (B : ?) (p : Sig (u : A). B) : Sig (v : B). A =
  (snd p, fst p)

proc withLet (A : ?) (x : A) : A =
  let y : A = x in y
""")
  assert prog.len == 4
  assert prog[0].def.name == "twice"
  assert $prog[0].def.desugarTy() == "Pi (A : ?). Pi (f : A -> A). Pi (x : A). A"
  assert $prog[0].def.desugarTm() ==
    "lam (A : ?). lam (f : A -> A). lam (x : A). f (f x)"
  assert $prog[1].def.desugarTm() ==
    "lam (A : ?). lam (B : ?). lam (x : A). lam (y : B). x"
  assert $prog[2].def.desugarTy() ==
    "Pi (A : ?). Pi (B : ?). Pi (p : Sig (u : A). B). Sig (v : B). A"
  assert $prog[2].def.desugarTm() ==
    "lam (A : ?). lam (B : ?). lam (p : Sig (u : A). B). (snd p, fst p)"
  assert $prog[3].def.desugarTm() ==
    "lam (A : ?). lam (x : A). let y : A = x in y"

  # locations are tracked (Nim's `"""` strips the leading newline)
  assert prog[0].def.body.loc.line == 2
  assert prog[0].def.body.loc.col == 3
  assert prog[2].def.name == "pairSwap"

  # errors point at source
  try:
    discard parseProgram("proc broken (A : ?) : A =\n  f (")
    assert false, "should have raised"
  except ParseError as e:
    assert "line 2" in e.msg, e.msg
    assert e.loc.line == 2

  try:
    discard parseProgram("proc broken : = x")
    assert false, "should have raised"
  except ParseError as e:
    assert "line 1" in e.msg

  # round trip through the renderer
  let rt = parseProgram("proc id (A : ?) (x : A) : A = x")
  assert $rt[0].def.desugarTm() == "lam (A : ?). lam (x : A). x"

  # implicit binders and holes (Experiment 3)
  let imp = parseProgram("""
proc polyId {A : ?} (x : A) : A = x
proc useHole : 1 = _
proc impPi : Pi {A : ?}. A -> A = lam {A : ?}. lam (x : A). x
""")
  assert imp.len == 3
  assert imp[0].def.tele[0].impl
  assert not imp[0].def.tele[1].impl
  assert $imp[0].def.desugarTy() == "Pi {A : ?}. Pi (x : A). A"
  assert $imp[0].def.desugarTm() == "lam {A : ?}. lam (x : A). x"
  assert imp[1].def.body.kind == pkHole
  assert $imp[2].def.desugarTy() == "Pi {A : ?}. A -> A"
  assert $imp[2].def.desugarTm() == "lam {A : ?}. lam (x : A). x"


  # postulate / elim / red declarations (Experiment 4)
  let decls = parseProgram("""
postulate Bool : ?
postulate true : Bool
elim boolElim : Pi (C : Bool -> ?). C true -> C false -> Pi (b : Bool). C b
red boolElim C t f true  = t
red boolElim C t f false = f
""")
  assert decls.len == 5
  assert decls[0].kind == dkPostulate and decls[0].name == "Bool"
  assert decls[2].kind == dkElim and decls[2].name == "boolElim"
  assert decls[3].kind == dkRed
  assert decls[3].lhs.kind == pkApp

  # import declarations (issue #49)
  let imps = parseProgram("import \"lib/nat.ep\"\nproc id (A : ?) (x : A) : A = x")
  assert imps.len == 2
  assert imps[0].kind == dkImport and imps[0].ipath == "lib/nat.ep"
  assert imps[1].kind == dkDef

  echo "parse_surf: all tests passed"
