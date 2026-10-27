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
# Surface syntax (Nim-consistent; single syntax, issues #467/#468/#469):
#   program = decl*
#   decl    = proc | def | mutual | postulate | elim | red | data | record | import
#   decl    = ... | postulate "(" name "," term ")" | elim "(" name "," term ")"
#             | red "(" term "," term ")" | data "(" name ["," "[" param "]"] "," term ")" "where" ctor*
#             | def "(" name "," term ")" ":" clause* | record "(" name ")" ":" field*
#   clause  = "clause" "(" "[" pattern ("," pattern)* "]" "," term ")"
#   param   = name ":" term
#   field   = name ":" term
#   import  = "import" string        -- multi-file programs (issue #49)
#   proc    = "proc" name tele ":" term "=" term
#   tele    = (binder)*
#   binder  = "(" name ":" term ")" | "{" name ":" term "}"  -- {} = implicit
#            | "(" qty name ":" term ")"  -- qty: 0 (erased), 1 (linear),
#                                            or a quantity variable (#66)
#   term    = arrow
#   arrow   = app ("->" arrow)?              -- right associative
#   app     = atom+   -- issue #467 (Nim call rule): a paren group with a
#                      top-level comma in argument position is a
#                      multi-argument call, not a pair argument
#   atom    = "(" term ")" | "(" term "," term ")" | "(" term ":" term ")"
#            | term "[" term ("," term)* "]"          -- bracket application
#            | "lam" "(" name "," term "," term ")" | "lam" "(" name "," term ")"
#            | "lam" "(" "{" name ":" term "}" "," term ")"
#            | "Pi" "(" binder-item ("," binder-item)* "," term ")"
#            | "Pi" "{" binder-item ("," binder-item)* "," term ")"
#            | "Sig" "(" ... ")"  (same items; also Sig(name, dom, body))
#            | "let" name (":" term)? "=" term "in" term
#            | "fst" atom | "snd" atom | "byTac" "(" tactic ")"
#            | "?" digits                              -- named hole
#            | "_"                                     -- hole in terms, discard in patterns
#            | name | "unitTy" | "unitv" | "emptyTy" | "Univ" | "vecnil"
#            | integer                                 -- `1` is the integer literal one
#   binder-item = [qty] name ":" term | term          -- plain term = anonymous binder
#            -- qty: 0 (erased), 1 (linear), or a quantity variable
# Comments: `--` or `#` to end of line.
#
# eponymBlock Nim-AST mapping (eponym_mac.nim `blockToEponym`):
# Single syntax: the macro emits the grammar above directly. What remains
# is Nim-AST-to-text translation, not a second syntax:
#   `lam(x, T, body)` / `Pi(...)` / `Sig(...)` / `postulate` / `elim` /
#   `red` / `data` / `def` / `record` / `byTac` -> themselves (call forms)
#   `Univ` / `unitTy` / `unitv` / `emptyTy` / `vecnil` / `_` -> themselves
#     (the parser maps `vecnil` to the `nil` constructor internally)
#   `let y: T = v` (in proc bodies) -> let y : T = v in ...
#   `f(x, y)`             -> application `f x y` (tuple args get double
#                            parens: `f((a, b))` passes the pair, #467)
#   `Vec[Int, n]`         -> `Vec Int n` (bracket application)
#   `ch {.linear.}`       -> `1 ch` prefix in call-form binders
#   `ch {.erased.}`       -> `0 ch` prefix
#   `ch {.qvar(q).}`      -> `q ch` prefix (quantity *variable*, #151/#66)
#   `A -> B` (infix)      -> `A -> B` (right associative; arrows are shared)
#   `(a, b)`              -> pair; `fst p` / `snd p` -> projections
#   `nil` (Nim literal, typed let) -> `vecnil (...)` (nilConstructorForType)
#   `+` / `-` / `*`       -> addInt / subInt / mulInt applications
#   `if` expressions      -> eliminator / lam encodings (ifExprToEponym)
#   Nim proc headers      -> `proc` headers (same modulo whitespace;
#                            binder groups stay space-separated)
#   `import "path"`       -> import "path"
# Kept extensions (no block equivalent yet, #469): universe levels above 0
# (`Type 1`, `Type 2`), named holes (`?n`), quantity annotations vs
# pragmas (context-determined), interfaces, host directives. Proc
# statement bodies and header pragmas remain block-only: they are
# Nim-AST constructs, not surface syntax.
# If a new surface form is added to the grammar above, a mapping (or a
# documented reason it cannot be emitted) must be added here in the same
# commit.

import preterm, strutils, sets
import elab_prof  # Issue #55: phase timers

type
  TokKind = enum
    tkEof, tkIdent, tkInt, tkString,
    tkDef, tkClauses, tkPostulate, tkElim, tkRed, tkData, tkWhere, tkBy,
    tkRecord, tkMutual,
    tkImport, tkInterface, tkCommand,
    tkLam, tkPi, tkSig, tkLet, tkIn, tkFst, tkSnd,
    tkQuestion,
    tkLParen, tkRParen, tkLBrace, tkRBrace, tkLBracket, tkRBracket,
    tkColon, tkColonEq, tkDot, tkComma, tkArrow, tkEq, tkPipe
  Token = object
    kind: TokKind
    lexeme: string
    loc: Loc
  Parser = object
    toks: seq[Token]
    pos: int
    qvarCount: int  # Issue #84: fresh quantity-variable supply for
                    # unannotated binders (default is inference, not qOmega)
    inPattern: bool  # Issue #467: true while parsing clause patterns, so
                     # `_` stays a discard there (in terms it is a hole)
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
  ("record", tkRecord), ("mutual", tkMutual),
  ("import", tkImport), ("interface", tkInterface), ("command", tkCommand),
  ("lam", tkLam), ("Pi", tkPi), ("Sig", tkSig),
  ("let", tkLet), ("in", tkIn), ("fst", tkFst), ("snd", tkSnd)]

proc isIdentStart(c: char): bool = c.isAlphaAscii or c == '_'
proc isIdentChar(c: char): bool = c.isAlphaNumeric or c in {'_', '\''}

proc lex(src: string, source = ""): seq[Token] =
  var i = 0
  var line = 1
  var col = 1
  proc curLoc(): Loc = Loc(line: line, col: col, source: source)
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
      result.add Token(kind: k, lexeme: w, loc: l)
    elif c == '?':
      let l = curLoc()
      var j = i + 1
      while j < src.len and src[j] in {'0'..'9'}: inc j
      let suffix = src[i + 1 ..< j]
      result.add Token(kind: tkQuestion, lexeme: suffix, loc: l)
      col += j - i; i = j
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
      result.add Token(kind: tkInt, lexeme: w, loc: l)
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
    elif c == '[':
      result.add Token(kind: tkLBracket, lexeme: "[", loc: curLoc())
      inc col; inc i
    elif c == ']':
      result.add Token(kind: tkRBracket, lexeme: "]", loc: curLoc())
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
  k in {tkIdent, tkInt, tkQuestion, tkLParen,
        tkLam, tkPi, tkSig, tkFst, tkSnd}

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
  # Issue #84: an unannotated binder defaults to quantity *inference* (a
  # fresh quantity variable, solved from the bound variable's uses:
  # 0 -> q0, 1 -> q1, 2+ -> qOmega), not to concrete qOmega. Explicit
  # annotations (`0` / `1` / a named quantity variable) override. The `#`
  # prefix is not a legal identifier character (see isIdentChar), so a
  # generated name can never collide with a user-written quantity variable.
  var qty: Qty = qtyVar("#q" & $p.qvarCount)
  inc p.qvarCount
  let pk = p.peek()
  if not impl and pk.kind == tkInt:
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

proc groupHasTopComma(p: Parser): bool =
  ## Issue #467: true when the bracket group starting at the current peek
  ## contains a top-level comma before its matching close bracket.
  ## Depth-aware, so commas inside nested groups (e.g. a pair type) do not
  ## count. Tells call forms (`lam(x, T, body)`, `Pi(x: A, B)`,
  ## `red(l, r)`) apart from classic binder/paren groups
  ## (`lam (x : T). body`, `red (f x) = y`).
  if p.pos > p.toks.high: return false
  if p.toks[p.pos].kind notin {tkLParen, tkLBrace, tkLBracket}: return false
  var depth = 0
  var i = p.pos
  while i <= p.toks.high:
    let k = p.toks[i].kind
    if k in {tkLParen, tkLBrace, tkLBracket}: inc depth
    elif k in {tkRParen, tkRBrace, tkRBracket}:
      dec depth
      if depth == 0: return false
    elif k == tkComma and depth == 1: return true
    inc i
  false

proc itemIsLast(p: Parser): bool =
  ## Issue #467: true when the item starting at the current peek ends at
  ## the enclosing group's close bracket (no top-level comma follows it).
  ## Lets the Pi/Sig call-form parser tell binders from the body while
  ## assigning quantity variables in source order.
  var depth = 0
  var i = p.pos
  while i <= p.toks.high:
    let k = p.toks[i].kind
    if k in {tkLParen, tkLBrace, tkLBracket}: inc depth
    elif k in {tkRParen, tkRBrace, tkRBracket}:
      if depth == 0: return true
      dec depth
    elif k == tkComma and depth == 0: return false
    inc i
  true

proc isPositionalSig(p: Parser): bool =
  ## Issue #467: true when the group starting at the current peek is a
  ## `Sig(name, dom, body)` group: exactly three items, the first a single
  ## identifier. Token-level lookahead; consumes nothing.
  if p.pos > p.toks.high or p.toks[p.pos].kind != tkLParen: return false
  if p.pos + 2 > p.toks.high: return false
  if p.toks[p.pos + 1].kind != tkIdent: return false
  if p.toks[p.pos + 2].kind != tkComma: return false
  var depth = 0
  var commas = 0
  var i = p.pos
  while i <= p.toks.high:
    let k = p.toks[i].kind
    if k in {tkLParen, tkLBrace, tkLBracket}: inc depth
    elif k in {tkRParen, tkRBrace, tkRBracket}:
      dec depth
      if depth == 0: return commas == 2
    elif k == tkComma and depth == 1: inc commas
    inc i
  false

proc parsePiSigCallForm(p: var Parser, isPi: bool, loc: Loc): PreTerm =
  ## Issue #467: `Pi`/`Sig` in call form — `Pi(x: A, y: B, C)`,
  ## `Sig(x: A, B)`, `Sig(A, B)` (anonymous binder), `Sig(u, A, B)` (the
  ## macro's positional Sig form), `Pi{A: T, B}` (implicit binders, Pi
  ## only). Items are `ident : term` binders or plain terms; the last
  ## item is the body. Quantity variables are assigned in source order
  ## (each binder's variable before its type is parsed), matching the
  ## dot-form parser, so conformance comparisons agree on quantities.
  ## Quantity-annotated binders are spelled `1 y: T`, `0 y: T`, `q y: T`
  ## (the macro's call-form spelling of `(1 y : T)` etc.); like the
  ## dot-form binder they consume a counter value, then override it with
  ## the annotation. Sigma drops quantities, as in the dot form.
  let positional = not isPi and p.isPositionalSig()
  let open = p.next()
  let impl = open.kind == tkLBrace
  if not isPi and impl:
    raise fail(loc, "implicit Sigma binders are not supported")
  let close = if impl: tkRBrace else: tkRParen
  if positional:
    # Sig(name, dom, body): one binder. Sigma carries no quantity, but the
    # dot-form parse consumes one counter value for the binder, so consume
    # one here to keep later binders aligned.
    let nm = p.expect(tkIdent, "binder name in 'Sig(...)'")
    discard p.expect(tkComma, "','")
    inc p.qvarCount
    let dom = p.parseTerm()
    discard p.expect(tkComma, "','")
    let body = p.parseTerm()
    discard p.expect(tkRParen, "')'")
    return mkSigma(nm.lexeme, dom, body, loc)
  var binders: seq[tuple[name: string, ty: PreTerm, qty: Qty,
                          erased: bool]] = @[]
  var body: PreTerm = nil
  var count = 0
  while true:
    inc count
    let last = p.itemIsLast()
    if ((p.peek().kind == tkInt) and
        p.pos + 2 <= p.toks.high and p.toks[p.pos + 1].kind == tkIdent and
        p.toks[p.pos + 2].kind == tkColon) or
       (p.peek().kind == tkIdent and p.pos + 2 <= p.toks.high and
        p.toks[p.pos + 1].kind == tkIdent and
        p.toks[p.pos + 2].kind == tkColon):
      # Quantity-annotated binder; see the doc comment above.
      inc p.qvarCount
      let qpk = p.next()
      var q: Qty
      var er = false
      if qpk.kind == tkIdent: q = qtyVar(qpk.lexeme)
      elif qpk.lexeme == "0": q = q0; er = true
      else: q = q1
      let nm = p.next()
      discard p.next()  # ':'
      if last:
        raise fail(loc, "Pi/Sig call form: body cannot be a binder")
      binders.add (nm.lexeme, p.parseTerm(), q, er)
    elif p.peek().kind == tkIdent and p.pos + 1 <= p.toks.high and
       p.toks[p.pos + 1].kind == tkColon:
      let nm = p.next()
      discard p.next()  # ':'
      if last:
        raise fail(loc, "Pi/Sig call form: body cannot be a binder")
      let q = qtyVar("#q" & $p.qvarCount)
      inc p.qvarCount
      binders.add (nm.lexeme, p.parseTerm(), q, false)
    elif p.peek().kind == tkIdent and p.pos + 1 <= p.toks.high and
         p.toks[p.pos + 1].kind in {tkComma, close}:
      if last:
        # Body position: parse as a term, so aliases (unitTy, Univ,
        # emptyTy, vecnil) map to their constants instead of becoming
        # variables (issue #467: `Sig(v: unitTy, unitTy)` elabbed
        # `unitTy` as unbound before this fix).
        body = p.parseTerm()
      else:
        let nm = p.next()
        let q = qtyVar("#q" & $p.qvarCount)
        inc p.qvarCount
        binders.add ("_", mkVar(nm.lexeme, loc), q, false)
    else:
      if last:
        body = p.parseTerm()
      else:
        let q = qtyVar("#q" & $p.qvarCount)
        inc p.qvarCount
        binders.add ("_", p.parseTerm(), q, false)
    if p.peek().kind == tkComma: discard p.next()
    else: break
  discard p.expect(close, "closing bracket")
  if count < 2 or body.isNil:
    raise fail(loc, "Pi/Sig call form needs binders and a body")
  result = body
  for i in countdown(binders.high, 0):
    let b = binders[i]
    if isPi: result = mkPi(b.name, b.ty, result, loc, impl, b.erased,
                           b.qty)
    else: result = mkSigma(b.name, b.ty, result, loc)

proc parseAtom(p: var Parser): PreTerm =
  let t = p.next()
  case t.kind
  of tkIdent:
    if t.lexeme == "_":
      # Issue #467: `_` is a hole in term positions (matching eponymBlock,
      # where Nim `_` converts to `?`); in pattern positions (parseClausesDef
      # sets inPattern) it stays a discard.
      if p.inPattern: mkDiscard(t.loc) else: mkHole(t.loc)
    elif t.lexeme == "unitTy": mkUnitTy(t.loc)
    elif t.lexeme == "unitv": mkUnitV(t.loc)
    elif t.lexeme == "emptyTy": mkEmptyTy(t.loc)
    elif t.lexeme == "Univ": mkUnivN(0, t.loc)
    elif t.lexeme == "vecnil": mkVar("nil", t.loc)
    elif t.lexeme == "byTac" and p.peek().kind == tkLParen:
      # Issue #467: byTac(tac) call form (tactic name or string).
      discard p.next()  # '('
      let tac = p.next()
      let tacName = case tac.kind
        of tkIdent, tkString: tac.lexeme
        else: raise fail(tac.loc, "expected tactic name in 'byTac(...)'")
      discard p.expect(tkRParen, "')'")
      PreTerm(loc: t.loc, kind: pkBy, name: tacName)
    elif t.lexeme == "Type" and p.peek().kind == tkInt:
      # Issue #52: `Type l` — the level-annotated universe. `Type` stays a
      # plain identifier unless directly followed by an integer literal
      # (`Type0` still lexes as one identifier; `Type` alone is a variable).
      # `Type 0` is removed; spell it `Univ`.
      let lvl = parseInt(p.peek().lexeme)
      if lvl == 0:
        raise fail(t.loc, "`Type 0` is removed; use `Univ`")
      discard p.next()  # consume the level literal
      mkUnivN(lvl, t.loc)
    else: mkVar(t.lexeme, t.loc)
  of tkQuestion:
    if t.lexeme == "":
      raise fail(t.loc, "anonymous `?` is removed; use `_` for holes " &
        "(`?n` for named holes)")
    else: mkNamedHole(t.lexeme, t.loc)
  of tkInt: mkInt(parseInt(t.lexeme), t.loc)
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
    # Single syntax: lam(x, T, body), lam(x, body) (unannotated), and
    # lam({A: T}, body) (implicit). The dot forms are removed.
    if p.peek().kind == tkLParen and p.groupHasTopComma():
      discard p.next()  # '('
      if p.peek().kind == tkLBrace:
        # Implicit binder group `lam({A: T}, body)` (single syntax: the
        # macro's spelling of `lam {A : T}. body`). Each pair gets its
        # own quantity variable, in source order like the dot form.
        discard p.next()  # '{'
        var pairs: seq[tuple[name: string, ty: PreTerm, qty: Qty]] = @[]
        while true:
          let qq = qtyVar("#q" & $p.qvarCount)
          inc p.qvarCount
          let bn = p.expect(tkIdent, "binder name in 'lam({...})'")
          discard p.expect(tkColon, "':'")
          pairs.add (bn.lexeme, p.parseTerm(), qq)
          if p.peek().kind == tkComma: discard p.next()
          else: break
        discard p.expect(tkRBrace, "'}'")
        discard p.expect(tkComma, "','")
        var body = p.parseTerm()
        discard p.expect(tkRParen, "')'")
        for i in countdown(pairs.high, 0):
          body = mkLam(pairs[i].name, pairs[i].ty, body, t.loc, true,
                       false, pairs[i].qty)
        return body
      # Quantity variable first, matching the dot-form binder order;
      # an explicit annotation (`1 y`, `0 y`, `q y`) overrides it.
      var q = qtyVar("#q" & $p.qvarCount)
      inc p.qvarCount
      var erased = false
      var annotated = false
      let pk = p.peek()
      if pk.kind == tkInt:
        let qlex = pk.lexeme
        if qlex == "0":
          discard p.next()
          erased = true
          q = q0
          annotated = true
        elif qlex == "1":
          discard p.next()
          q = q1
          annotated = true
      elif pk.kind == tkIdent and p.pos + 1 <= p.toks.high and
           p.toks[p.pos + 1].kind == tkIdent:
        q = qtyVar(pk.lexeme)
        discard p.next()  # quantity variable name
        annotated = true
      let xn = p.expect(tkIdent, "binder name in 'lam(...)'")
      discard p.expect(tkComma, "','")
      if p.itemIsLast():
        # Two-item form lam(x, body): unannotated lambda (the renderer's
        # spelling of the old `lam x. body`). Without an annotation the
        # quantity is qOmega, matching the old form's default.
        let body = p.parseTerm()
        discard p.expect(tkRParen, "')'")
        return mkLam(xn.lexeme, nil, body, t.loc, false, erased,
                     if annotated: q else: qOmega)
      let ty = p.parseTerm()
      discard p.expect(tkComma, "','")
      let body = p.parseTerm()
      discard p.expect(tkRParen, "')'")
      mkLam(xn.lexeme, ty, body, t.loc, false, erased, q)
    else:
      raise fail(t.loc, "lam needs call form lam(x, T, body) or lam(x, body)")
  of tkPi, tkSig:
    # Single syntax: Pi/Sig call forms only (the dot forms are removed).
    if p.peek().kind in {tkLParen, tkLBrace} and p.groupHasTopComma():
      p.parsePiSigCallForm(t.kind == tkPi, t.loc)
    else:
      raise fail(t.loc, "Pi/Sig need call form Pi(x: A, B) / Sig(x: A, B)")
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

proc parseProjTail(p: var Parser, e: PreTerm): PreTerm =
  ## Issue #37: postfix dot-projection `e.f` (also chains: `e.f.g`).
  ## The `lam x. body` / `Pi/Sig (x:T). body` dots are consumed inside
  ## parseAtom, so a dot here always starts a projection.
  result = e
  while p.peek().kind == tkDot:
    let dloc = p.next().loc
    let f = p.expect(tkIdent, "field name after '.'")
    result = mkProj(result, f.lexeme, dloc)

proc parseApp(p: var Parser): PreTerm =
  ## Issue #37: `.f` binds tighter than application: `g x.f` is `g (x.f)`.
  ## The tail applies to each argument atom, never to an application node.
  result = p.parseProjTail(p.parseAtom())
  while true:
    if p.peek().kind.isAtomStart():
      let loc = result.loc
      if p.peek().kind == tkLParen and p.groupHasTopComma():
        # Issue #467 (Nim call rule): a comma group in argument position
        # is a multi-argument call `f(a, b)` = `f a b`, not `f` applied
        # to the pair. A pair argument needs double parens `f((a, b))`.
        # (A group in first-atom position is still a pair value.)
        discard p.next()  # '('
        while true:
          result = mkApp(result, p.parseTerm(), loc)
          if p.peek().kind == tkComma: discard p.next()
          else: break
        discard p.expect(tkRParen, "')'")
      else:
        result = mkApp(result, p.parseProjTail(p.parseAtom()), loc)
    elif p.peek().kind == tkLBracket:
      # Issue #467: bracket application `Vec[Int, n]` (the embedded form).
      # Safe: `[` has no other term-position meaning (pegs are consumed by
      # parsePeg before the return type, never inside a term).
      discard p.next()  # '['
      while true:
        let loc = result.loc
        result = mkApp(result, p.parseTerm(), loc)
        if p.peek().kind == tkComma: discard p.next()
        else: break
      discard p.expect(tkRBracket, "']'")
    else: break

proc parseTerm(p: var Parser): PreTerm =
  let lhs = p.parseApp()
  if p.peek().kind == tkArrow:
    let t = p.next()
    if lhs.kind == pkAnn:
      # The binder-arrow form `(x : A) -> B` (issue #65) is removed; it
      # would now parse as an ascription followed by an arrow, which is
      # almost never intended — spell it Pi(x: A, B).
      raise fail(t.loc, "binder-arrow `(x : A) -> B` is removed; " &
        "use Pi(x: A, B)")
    mkArrow(lhs, p.parseTerm(), t.loc)
  else:
    lhs

proc parsePeg(p: var Parser): tuple[hasPeg: bool, names: seq[string]] =
  ## Issue #177: parse `[I1, I2]` (possibly empty `[]`) after ':' in a
  ## `proc` signature. Returns hasPeg=false when there is no bracket.
  if p.peek().kind != tkLBracket:
    return (false, @[])
  discard p.next()
  var names: seq[string] = @[]
  if p.peek().kind != tkRBracket:
    while true:
      let n = p.expect(tkIdent, "interface name in peg")
      names.add n.lexeme
      if p.peek().kind == tkComma: discard p.next()
      else: break
  discard p.expect(tkRBracket, "']'")
  (true, names)

proc parseDef(p: var Parser): SurfDef =
  let t = p.expect(tkDef, "'proc'")
  let nm = p.expect(tkIdent, "definition name")
  var tele: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool, qty: Qty]] = @[]
  while p.peek().kind in {tkLParen, tkLBrace}:
    let b = p.parseBinder()
    tele.add b
  discard p.expect(tkColon, "':'")
  let (hasPeg, pegNames) = p.parsePeg()  # Issue #177
  let retTy = p.parseTerm()
  discard p.expect(tkEq, "'='")
  let body = p.parseTerm()
  SurfDef(name: nm.lexeme, tele: tele, retTy: retTy, body: body, loc: t.loc,
          hasPeg: hasPeg, pegNames: pegNames)

proc parseInterface(p: var Parser): SurfDecl =
  ## Issue #177: `interface Name`.
  let t = p.expect(tkInterface, "'interface'")
  let nm = p.expect(tkIdent, "interface name")
  SurfDecl(kind: dkInterface, ifname: nm.lexeme, ifloc: t.loc)

proc parseCommand(p: var Parser): SurfDecl =
  ## Issue #177: `command c : A -> B in I`.
  let t = p.expect(tkCommand, "'command'")
  let nm = p.expect(tkIdent, "command name")
  discard p.expect(tkColon, "':'")
  let ty = p.parseTerm()
  discard p.expect(tkIn, "'in'")
  let iface = p.expect(tkIdent, "interface name")
  SurfDecl(kind: dkCommand, cname: nm.lexeme, cty: ty, ciface: iface.lexeme,
           cloc: t.loc)

proc parsePostulate(p: var Parser): SurfDecl =
  let t = p.expect(tkPostulate, "'postulate'")
  if p.peek().kind == tkLParen:
    # Issue #467: postulate(N, T) call form.
    discard p.next()
    let nm = p.expect(tkIdent, "postulate name")
    discard p.expect(tkComma, "','")
    let ty = p.parseTerm()
    discard p.expect(tkRParen, "')'")
    return SurfDecl(kind: dkPostulate, name: nm.lexeme, ty: ty, dloc: t.loc)
  raise fail(t.loc, "postulate needs call form postulate(N, T)")

proc parseElim(p: var Parser): SurfDecl =
  let t = p.expect(tkElim, "'elim'")
  if p.peek().kind == tkLParen:
    # Issue #467: elim(N, T) call form.
    discard p.next()
    let nm = p.expect(tkIdent, "eliminator name")
    discard p.expect(tkComma, "','")
    let ty = p.parseTerm()
    discard p.expect(tkRParen, "')'")
    return SurfDecl(kind: dkElim, name: nm.lexeme, ty: ty, dloc: t.loc)
  raise fail(t.loc, "elim needs call form elim(N, T)")

proc parseRed(p: var Parser): SurfDecl =
  let t = p.expect(tkRed, "'red'")
  if p.peek().kind == tkLParen and p.groupHasTopComma():
    # Issue #467: red(lhs, rhs) call form. Terms inside stay .ep terms
    # (space application); only the wrapper is the embedded form.
    discard p.next()
    let lhs = p.parseTerm()
    discard p.expect(tkComma, "','")
    let rhs = p.parseTerm()
    discard p.expect(tkRParen, "')'")
    return SurfDecl(kind: dkRed, lhs: lhs, rhs: rhs, rloc: t.loc)
  raise fail(t.loc, "red needs call form red(lhs, rhs)")

proc parseData(p: var Parser): SurfDecl =
  ## data(Vec, [A: Univ], Nat -> Univ) where
  ## | nil : Vec A zero
  ## | cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
  let t = p.expect(tkData, "'data'")
  var nm: Token
  var params: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool, qty: Qty]] = @[]
  var indexTy: PreTerm
  if p.peek().kind == tkLParen:
    # Issue #467: data(N, K) / data(N, [A: T, ...], K) call form, then the
    # usual `where | ctor` body.
    discard p.next()
    nm = p.expect(tkIdent, "datatype name")
    discard p.expect(tkComma, "','")
    if p.peek().kind == tkLBracket:
      discard p.next()
      # An empty list `[]` means no parameters.
      if p.peek().kind != tkRBracket:
        while true:
          let pn = p.expect(tkIdent, "parameter name")
          discard p.expect(tkColon, "':'")
          # Quantity variable first, matching the dot-form binder order.
          let q = qtyVar("#q" & $p.qvarCount)
          inc p.qvarCount
          let pty = p.parseTerm()
          params.add (pn.lexeme, pty, false, false, q)
          if p.peek().kind == tkComma: discard p.next()
          else: break
      discard p.expect(tkRBracket, "']'")
      discard p.expect(tkComma, "','")
    indexTy = p.parseTerm()
    discard p.expect(tkRParen, "')'")
  else:
    raise fail(t.loc, "data needs call form data(N, K) / data(N, [A: T, ...], K)")
  discard p.expect(tkWhere, "'where'")
  var ctors: seq[DataCtor] = @[]
  while p.peek().kind == tkPipe:
    discard p.next()
    let cnm = p.expect(tkIdent, "constructor name")
    # `vecnil` is the surface spelling of the `nil` constructor (the
    # macro's Nim-safe name); references map the same way in parseAtom.
    let cname = if cnm.lexeme == "vecnil": "nil" else: cnm.lexeme
    var tele: seq[tuple[name: string, ty: PreTerm, impl: bool, erased: bool, qty: Qty]] = @[]
    while p.peek().kind in {tkLParen, tkLBrace}:
      tele.add p.parseBinder()
    discard p.expect(tkColon, "':'")
    let retTy = p.parseTerm()
    ctors.add DataCtor(name: cname, tele: tele, retTy: retTy,
                       cloc: cnm.loc)
  if ctors.len == 0:
    raise fail(t.loc, "data declaration needs at least one constructor")
  SurfDecl(kind: dkData, dname: nm.lexeme, params: params, indexTy: indexTy,
           ctors: ctors, daloc: t.loc)

proc parseRecord(p: var Parser): SurfDecl =
  ## Issue #37:
  ## record Point:
  ## | x : Int
  ## | y : Int
  let t = p.expect(tkRecord, "'record'")
  var nm: Token
  if p.peek().kind == tkLParen:
    # Issue #467: record(N) call form, then the usual `: | field` body.
    discard p.next()
    nm = p.expect(tkIdent, "record name")
    discard p.expect(tkRParen, "')'")
  else:
    raise fail(t.loc, "record needs call form record(N)")
  discard p.expect(tkColon, "':'")
  var fields: seq[RecordField] = @[]
  while p.peek().kind == tkPipe:
    discard p.next()
    let fnm = p.expect(tkIdent, "field name")
    discard p.expect(tkColon, "':'")
    let fty = p.parseTerm()
    for f in fields:
      if f.name == fnm.lexeme:
        raise fail(fnm.loc, "duplicate field '" & fnm.lexeme &
          "' in record '" & nm.lexeme & "'")
    fields.add RecordField(name: fnm.lexeme, ty: fty, floc: fnm.loc)
  if fields.len == 0:
    raise fail(t.loc, "record declaration needs at least one field")
  SurfDecl(kind: dkRecord, rname: nm.lexeme, fields: fields, recloc: t.loc)

proc parseClausesDef(p: var Parser): ClausesDef =
  ## `def name : Ty` followed by `| pat1 .. patn = rhs` clauses.
  ## Each pattern is an atom; constructor applications need parens: `(suc m)`.
  ## Issue #467: `def(N, T):` followed by `clause([pats], rhs)` items (the
  ## embedded form). Patterns parse with inPattern set, so `_` stays a
  ## discard there; in clause right-hand sides it is a hole.
  let t = p.expect(tkClauses, "'def'")
  var nm: Token
  var ty: PreTerm
  var clauses: seq[Clause] = @[]
  if p.peek().kind == tkLParen:
    discard p.next()
    nm = p.expect(tkIdent, "definition name")
    discard p.expect(tkComma, "','")
    ty = p.parseTerm()
    discard p.expect(tkRParen, "')'")
    discard p.expect(tkColon, "':'")
    while p.peek().kind == tkIdent and p.peek().lexeme == "clause":
      let cloc = p.next().loc
      discard p.expect(tkLParen, "'('")
      discard p.expect(tkLBracket, "'['")
      var pats: seq[PreTerm] = @[]
      p.inPattern = true
      while p.peek().kind != tkRBracket:
        # Call-form patterns are comma-separated, so each pattern is a full
        # application (`suc(n)`), unlike classic `|`-clauses where patterns
        # are space-separated atoms and `suc n` needs parens.
        pats.add p.parseApp()
        if p.peek().kind == tkComma: discard p.next()
        else: break
      p.inPattern = false
      discard p.expect(tkRBracket, "']'")
      discard p.expect(tkComma, "','")
      let rhs = p.parseTerm()
      discard p.expect(tkRParen, "')'")
      if pats.len == 0:
        raise fail(cloc, "clause needs at least one pattern")
      clauses.add Clause(pats: pats, rhs: rhs, cloc: cloc)
    if clauses.len == 0:
      raise fail(t.loc, "'def(N, T):' needs at least one 'clause(...)' item")
  else:
    raise fail(t.loc, "def needs call form def(N, T): clause([pats], rhs)")
  ClausesDef(name: nm.lexeme, ty: ty, clauses: clauses, loc: t.loc)

proc parseClauses(p: var Parser): SurfDecl =
  SurfDecl(kind: dkClauses, clausesDef: p.parseClausesDef())

proc parseMutual(p: var Parser): SurfDecl =
  ## Issue #42: `mutual` block of clause-style `def`s. Each `def` starts
  ## a new group; the block ends at the first non-`def` token.
  let t = p.expect(tkMutual, "'mutual'")
  var defs: seq[ClausesDef] = @[]
  while p.peek().kind == tkClauses:
    defs.add p.parseClausesDef()
  if defs.len == 0:
    raise fail(t.loc, "'mutual' needs at least one 'def' group")
  var seen = initHashSet[string]()
  for cd in defs:
    if cd.name in seen:
      raise fail(cd.loc, "duplicate definition '" & cd.name &
        "' in mutual block")
    seen.incl(cd.name)
  SurfDecl(kind: dkMutual, mutualDefs: defs, mutualLoc: t.loc)

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
  of tkRecord: p.parseRecord()
  of tkMutual: p.parseMutual()
  of tkImport: p.parseImport()
  of tkInterface: p.parseInterface()
  of tkCommand: p.parseCommand()
  else: raise fail(p.peek().loc, "expected 'proc', 'def', 'postulate', 'elim', 'red', 'data', 'record', 'mutual', 'import', 'interface' or 'command'")

proc parseProgram*(src: string, source = ""): seq[SurfDecl] =
  profilePhase(epParse):
      ## Parse a whole program; raises ParseError with source location.
      var p = Parser(toks: lex(src, source), pos: 0)
      while p.peek().kind != tkEof:
        result.add p.parseDecl()

proc parseTermStr*(src: string): PreTerm =
  ## Issue #50: parse a single surface term (for the REPL's `:type`/`:eval`).
  ## Raises ParseError with source location; trailing tokens are an error.
  var p = Parser(toks: lex(src), pos: 0)
  result = p.parseTerm()
  if p.peek().kind != tkEof:
    raise fail(p.peek().loc, "expected end of input after term")

# --- tests ------------------------------------------------------------

when isMainModule:
  let prog = parseProgram("""
proc twice (A : Univ) (f : A -> A) (x : A) : A =
  f (f x)

-- const and pairSwap
proc const (A : Univ) (B : Univ) (x : A) (y : B) : A =
  x

proc pairSwap (A : Univ) (B : Univ) (p : Sig(u, A, B)) : Sig(v, B, A) =
  (snd p, fst p)

proc withLet (A : Univ) (x : A) : A =
  let y : A = x in y
""")
  assert prog.len == 4
  assert prog[0].def.name == "twice"
  assert $prog[0].def.desugarTy() == "Pi(A: Univ, Pi(f: A -> A, Pi(x: A, A)))"
  assert $prog[0].def.desugarTm() ==
    "lam(A, Univ, lam(f, A -> A, lam(x, A, f (f x))))"
  assert $prog[1].def.desugarTm() ==
    "lam(A, Univ, lam(B, Univ, lam(x, A, lam(y, B, x))))"
  assert $prog[2].def.desugarTy() ==
    "Pi(A: Univ, Pi(B: Univ, Pi(p: Sig(u: A, B), Sig(v: B, A))))"
  assert $prog[2].def.desugarTm() ==
    "lam(A, Univ, lam(B, Univ, lam(p, Sig(u: A, B), (snd p, fst p))))"
  assert $prog[3].def.desugarTm() ==
    "lam(A, Univ, lam(x, A, let y : A = x in y))"

  # locations are tracked (Nim's `"""` strips the leading newline)
  assert prog[0].def.body.loc.line == 2
  assert prog[0].def.body.loc.col == 3
  assert prog[2].def.name == "pairSwap"

  # errors point at source
  try:
    discard parseProgram("proc broken (A : Univ) : A =\n  f (")
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
  let rt = parseProgram("proc id (A : Univ) (x : A) : A = x")
  assert $rt[0].def.desugarTm() == "lam(A, Univ, lam(x, A, x))"

  # implicit binders and holes (Experiment 3)
  let imp = parseProgram("""
proc polyId {A : Univ} (x : A) : A = x
proc useHole : unitTy = _
proc impPi : Pi{A: Univ, A -> A} = lam({A: Univ}, lam(x, A, x))
""")
  assert imp.len == 3
  assert imp[0].def.tele[0].impl
  assert not imp[0].def.tele[1].impl
  assert $imp[0].def.desugarTy() == "Pi{A: Univ, Pi(x: A, A)}"
  assert $imp[0].def.desugarTm() == "lam({A: Univ}, lam(x, A, x))"
  assert imp[1].def.body.kind == pkHole
  assert $imp[2].def.desugarTy() == "Pi{A: Univ, A -> A}"
  assert $imp[2].def.desugarTm() == "lam({A: Univ}, lam(x, A, x))"


  # postulate / elim / red declarations (Experiment 4)
  let decls = parseProgram("""
postulate(Bool, Univ)
postulate(true, Bool)
elim(boolElim, Pi(C: Bool -> Univ, C(true) -> C(false) -> Pi(b: Bool, C(b))))
red(boolElim C t f true, t)
red(boolElim C t f false, f)
""")
  assert decls.len == 5
  assert decls[0].kind == dkPostulate and decls[0].name == "Bool"
  assert decls[2].kind == dkElim and decls[2].name == "boolElim"
  assert decls[3].kind == dkRed
  assert decls[3].lhs.kind == pkApp

  # import declarations (issue #49)
  let imps = parseProgram("import \"lib/nat.ep\"\nproc id (A : Univ) (x : A) : A = x")
  assert imps.len == 2
  assert imps[0].kind == dkImport and imps[0].ipath == "lib/nat.ep"
  assert imps[1].kind == dkDef

  # embedded-block forms in .ep text (issue #467, additive acceptance)
  assert parseTermStr("unitTy").kind == pkUnitTy
  assert parseTermStr("unitv").kind == pkUnitV
  assert parseTermStr("emptyTy").kind == pkEmptyTy
  assert parseTermStr("Univ").kind == pkUnivN and
    parseTermStr("Univ").intVal == 0
  let vn = parseTermStr("vecnil")
  assert vn.kind == pkVar and vn.name == "nil"
  assert parseTermStr("_").kind == pkHole
  let lamCf = parseTermStr("lam(x, A, x)")
  assert lamCf.kind == pkLam and lamCf.name == "x"
  let piCf = parseTermStr("Pi(x: Nat, Nat)")
  assert piCf.kind == pkPi and piCf.name == "x"
  let sigAnon = parseTermStr("Sig(A, B)")
  assert sigAnon.kind == pkSigma and sigAnon.name == "_"
  let sigNamed = parseTermStr("Sig(u, A, B)")
  assert sigNamed.kind == pkSigma and sigNamed.name == "u"
  assert parseTermStr("Vec[Int, n]").kind == pkApp
  let by1 = parseTermStr("byTac(refl)")
  assert by1.kind == pkBy and by1.name == "refl"
  let by2 = parseTermStr("byTac(\"assumption\")")
  assert by2.kind == pkBy and by2.name == "assumption"

  let acc = parseProgram("""
proc unitVal : unitTy = unitv
proc absurd (x : emptyTy) : emptyTy = x
proc holeTy : Univ = _
postulate(Bool, Univ)
elim(boolElim, Pi(C: Bool -> Univ, C(true) -> C(false) -> Pi(b: Bool, C(b))))
red(boolElim C t f true, t)
data(Nat2, Univ) where
| zero2 : Nat2
| suc2 (n : Nat2) : Nat2
data(Vec2, [A: Univ], Pi(n: Nat, Vec2[A, n] -> Univ)) where
| vecnil : Vec2[A, zero]
| cons2 (n : Nat) (x : A) (xs : Vec2[A, n]) : Vec2[A, suc(n)]
def(isZero3, Nat -> Bool):
  clause([zero], true)
  clause([suc(n)], false)
  clause([_], true)
record(Point2):
| x : Univ
| y : Univ
""")
  assert acc.len == 10
  assert acc[0].def.body.kind == pkUnitV
  assert acc[0].def.retTy.kind == pkUnitTy
  assert acc[1].def.tele[0].ty.kind == pkEmptyTy
  assert acc[2].def.body.kind == pkHole
  assert acc[3].kind == dkPostulate and acc[3].name == "Bool"
  assert acc[4].kind == dkElim and acc[4].name == "boolElim"
  assert acc[5].kind == dkRed and acc[5].lhs.kind == pkApp
  assert acc[6].kind == dkData and acc[6].dname == "Nat2" and
    acc[6].ctors.len == 2
  assert acc[7].kind == dkData and acc[7].dname == "Vec2" and
    acc[7].params.len == 1 and acc[7].params[0].name == "A" and
    acc[7].ctors.len == 2 and acc[7].ctors[0].name == "nil"
  assert acc[8].kind == dkClauses and
    acc[8].clausesDef.name == "isZero3" and
    acc[8].clausesDef.clauses.len == 3 and
    acc[8].clausesDef.clauses[2].pats[0].kind == pkDiscard
  assert acc[9].kind == dkRecord and acc[9].rname == "Point2" and
    acc[9].fields.len == 2

  # `_` stays a discard in call-form `clause` patterns
  let cl = parseProgram("""
def(isZero4, Nat -> Bool):
  clause([zero], true)
  clause([_], false)
""")
  assert cl[0].clausesDef.clauses[1].pats[0].kind == pkDiscard

  # Nim call rule (issue #467): a comma group in argument position splits.
  let call2 = parseTermStr("f(a, b)")
  assert call2.kind == pkApp and call2.c1.kind == pkApp  # f a b
  let callPair = parseTermStr("f((a, b))")
  assert callPair.kind == pkApp and callPair.c2.kind == pkPair  # f (a, b)
  let callMixed = parseTermStr("f(a, (b, c))")
  assert callMixed.kind == pkApp and callMixed.c2.kind == pkPair
  let pairVal = parseTermStr("(a, b)")
  assert pairVal.kind == pkPair
  let fstPair = parseTermStr("fst (a, b)")
  assert fstPair.kind == pkFst and fstPair.c1.kind == pkPair

  # Removed forms raise (single syntax, issues #468/#469).
  for bad in ["lam (x : A). x", "Pi (x : A). B", "Sig (x : A). B",
              "Type 0", "<>", "?", "by refl", "(x : A) -> B"]:
    try:
      discard parseTermStr(bad)
      assert false, "should have raised for: " & bad
    except ParseError: discard
  for bad in ["postulate Bool : Univ", "elim e : Univ",
              "red f x = y", "data Nat : Univ where | zero : Nat",
              "record P : | x : Univ",
              "def f : Nat | zero = true"]:
    try:
      discard parseProgram(bad)
      assert false, "should have raised for: " & bad
    except ParseError: discard

  echo "parse_surf: all tests passed"
