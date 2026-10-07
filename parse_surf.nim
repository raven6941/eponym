# parse_surf.nim — front end (a): hand-written parser for a small surface
# syntax, producing preterm.PreTerm / SurfDef.
#
# Surface syntax:
#   program := def+
#   def     := "def" name tele ":" term ":=" term
#   tele    := (binder)*
#   binder  := "(" name ":" term ")" | "{" name ":" term "}"  -- {} = implicit
#   term    := arrow
#   arrow   := app ("->" arrow)?              -- right associative
#   app     := atom+
#   atom    := "(" term ")" | "(" term "," term ")" | "(" term ":" term ")"
#            | "lam" binder "." term | "Pi" binder "." term
#            | "Sig" "(" name ":" term ")" "." term
#            | "let" name (":" term)? "=" term "in" term
#            | "fst" atom | "snd" atom
#            | "_"                                     -- hole (Experiment 3)
#            | name | "?" | "1" | "<>" | "O"
# Comments: `--` to end of line.

import preterm, strutils

type
  TokKind = enum
    tkEof, tkIdent,
    tkDef, tkLam, tkPi, tkSig, tkLet, tkIn, tkFst, tkSnd,
    tkUniv, tkUnitTy, tkUnitV, tkEmptyTy,
    tkLParen, tkRParen, tkLBrace, tkRBrace,
    tkColon, tkColonEq, tkDot, tkComma, tkArrow, tkEq
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
  ("def", tkDef), ("lam", tkLam), ("Pi", tkPi), ("Sig", tkSig),
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
      while i < src.len and src[i] != '\n': inc i  # comment
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
    elif c == '1':
      result.add Token(kind: tkUnitTy, lexeme: "1", loc: curLoc())
      inc col; inc i
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
  k in {tkIdent, tkUniv, tkUnitTy, tkUnitV, tkEmptyTy, tkLParen,
        tkLam, tkPi, tkSig, tkFst, tkSnd}

proc parseTerm(p: var Parser): PreTerm  # forward

proc parseBinder(p: var Parser): tuple[name: string, ty: PreTerm, impl: bool] =
  ## "(" name ":" term ")" | "{" name ":" term "}"  (braces = implicit)
  let t = p.next()
  let impl = t.kind == tkLBrace
  if not impl and t.kind != tkLParen:
    raise fail(t.loc, "expected '(' or '{', got '" & t.lexeme & "'")
  let xn = p.expect(tkIdent, "binder name")
  discard p.expect(tkColon, "':'")
  let ty = p.parseTerm()
  if impl: discard p.expect(tkRBrace, "'}'")
  else: discard p.expect(tkRParen, "')'")
  (xn.lexeme, ty, impl)

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
      mkLam(b.name, b.ty, p.parseTerm(), t.loc, b.impl)
  of tkPi, tkSig:
    let b = p.parseBinder()
    if b.impl and t.kind == tkSig:
      raise fail(t.loc, "implicit Sigma binders are not supported")
    discard p.expect(tkDot, "'.'")
    let body = p.parseTerm()
    case t.kind
    of tkPi: mkPi(b.name, b.ty, body, t.loc, b.impl)
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

proc parseTerm(p: var Parser): PreTerm =
  let lhs = p.parseApp()
  if p.peek().kind == tkArrow:
    let t = p.next()
    mkArrow(lhs, p.parseTerm(), t.loc)
  else:
    lhs

proc parseDef(p: var Parser): SurfDef =
  let t = p.expect(tkDef, "'def'")
  let nm = p.expect(tkIdent, "definition name")
  var tele: seq[tuple[name: string, ty: PreTerm, impl: bool]] = @[]
  while p.peek().kind in {tkLParen, tkLBrace}:
    let b = p.parseBinder()
    tele.add b
  discard p.expect(tkColon, "':'")
  let retTy = p.parseTerm()
  discard p.expect(tkColonEq, "':='")
  let body = p.parseTerm()
  SurfDef(name: nm.lexeme, tele: tele, retTy: retTy, body: body, loc: t.loc)

proc parseProgram*(src: string): seq[SurfDef] =
  ## Parse a whole program; raises ParseError with source location.
  var p = Parser(toks: lex(src), pos: 0)
  while p.peek().kind != tkEof:
    result.add p.parseDef()

# --- tests ------------------------------------------------------------

when isMainModule:
  let prog = parseProgram("""
def twice (A : ?) (f : A -> A) (x : A) : A :=
  f (f x)

-- const and pairSwap
def const (A : ?) (B : ?) (x : A) (y : B) : A :=
  x

def pairSwap (A : ?) (B : ?) (p : Sig (u : A). B) : Sig (v : B). A :=
  (snd p, fst p)

def withLet (A : ?) (x : A) : A :=
  let y : A = x in y
""")
  assert prog.len == 4
  assert prog[0].name == "twice"
  assert $prog[0].desugarTy() == "Pi (A : ?). Pi (f : A -> A). Pi (x : A). A"
  assert $prog[0].desugarTm() ==
    "lam (A : ?). lam (f : A -> A). lam (x : A). f (f x)"
  assert $prog[1].desugarTm() ==
    "lam (A : ?). lam (B : ?). lam (x : A). lam (y : B). x"
  assert $prog[2].desugarTy() ==
    "Pi (A : ?). Pi (B : ?). Pi (p : Sig (u : A). B). Sig (v : B). A"
  assert $prog[2].desugarTm() ==
    "lam (A : ?). lam (B : ?). lam (p : Sig (u : A). B). (snd p, fst p)"
  assert $prog[3].desugarTm() ==
    "lam (A : ?). lam (x : A). let y : A = x in y"

  # locations are tracked (Nim's `"""` strips the leading newline)
  assert prog[0].body.loc.line == 2
  assert prog[0].body.loc.col == 3
  assert prog[2].name == "pairSwap"

  # errors point at source
  try:
    discard parseProgram("def broken (A : ?) : A :=\n  f (")
    assert false, "should have raised"
  except ParseError as e:
    assert "line 2" in e.msg, e.msg
    assert e.loc.line == 2

  try:
    discard parseProgram("def broken : := x")
    assert false, "should have raised"
  except ParseError as e:
    assert "line 1" in e.msg

  # round trip through the renderer
  let rt = parseProgram("def id (A : ?) (x : A) : A := x")
  assert $rt[0].desugarTm() == "lam (A : ?). lam (x : A). x"

  # implicit binders and holes (Experiment 3)
  let imp = parseProgram("""
def polyId {A : ?} (x : A) : A := x
def useHole : 1 := _
def impPi : Pi {A : ?}. A -> A := lam {A : ?}. lam (x : A). x
""")
  assert imp.len == 3
  assert imp[0].tele[0].impl
  assert not imp[0].tele[1].impl
  assert $imp[0].desugarTy() == "Pi {A : ?}. Pi (x : A). A"
  assert $imp[0].desugarTm() == "lam {A : ?}. lam (x : A). x"
  assert imp[1].body.kind == pkHole
  assert $imp[2].desugarTy() == "Pi {A : ?}. A -> A"
  assert $imp[2].desugarTm() == "lam {A : ?}. lam (x : A). x"

  echo "parse_surf: all tests passed"
