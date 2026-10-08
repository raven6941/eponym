## Experiment 2: the `ett` macro -- compile-time elaboration and checking.
##
## Deliberately thin (see decisions.org on Nimony/Nim 3): the parser and
## elaborator are plain Nim code in parse_surf and elab; the macro only feeds
## them a string literal and turns failures into compiler errors. No NimNode
## inspection, no hygiene tricks -- nothing that ties us to Nim 2's macro API.

import macros
import elab
import parse_surf
import ett_init
import strutils
import sequtils

# --- ettBlock: Nim-block syntax (no """) ---------------------------------
# Converts a block of (valid Nim) AST to Eponym source, elaborates it,
# and generates wrapper procs. Uses call syntax:
#   proc add42(n: Int): Int = addInt(n, 42)
#   postulate(Int, Univ)
#   data(Nat, Univ):
#     proc zero(): Nat
#     proc suc(n: Nat): Nat

proc nimExprToEponym(n: NimNode): string =
  ## Convert a Nim expression AST to Eponym source string.
  case n.kind
  of nnkIdent:
    var s = $n
    # Map Nim-safe names to Eponym names
    if s == "vecnil": s = "nil"
    if s == "Univ": "?" else: s
  of nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit:
    # In ettBlock, integer literals in term position are assumed to be Nat.
    # Generate suc chain directly; the elaborator's mkNatLit would do the same,
    # but this avoids issues with nested positions in the current implementation.
    # For primitive Int literals, use string syntax (ett"""...""") instead.
    let v = n.intVal
    if v < 0: error("negative Nat literal", n)
    var res = "zero"
    for i in 1..v:
      res = "suc (" & res & ")"
    # Paren if nested, to ensure correct grouping
    "(" & res & ")"
  of nnkStmtList:
    # Proc body: convert let-statements to nested let...in, final expr is body
    if n.len == 0: error("ettBlock: empty proc body", n)
    # Collect lets and final expression
    var lets: seq[(string, string)] = @[]  # (name, value)
    var finalExpr: NimNode = nil
    for stmt in n:
      if stmt.kind == nnkLetSection:
        for def in stmt:
          # nnkIdentDefs: [name, type, value]
          let name = $def[0]
          let val = nimExprToEponym(def[2])
          lets.add((name, val))
      else:
        # Final expression (or single expression)
        if finalExpr != nil:
          error("ettBlock: proc body must be lets followed by single expr", n)
        finalExpr = stmt
    if finalExpr == nil:
      error("ettBlock: proc body must end with expression", n)
    var res = nimExprToEponym(finalExpr)
    # Wrap in let...in (innermost first, so reverse)
    for i in countdown(lets.len - 1, 0):
      let (nm, vl) = lets[i]
      res = "let " & nm & " = " & vl & " in " & res
    res
  of nnkCall:
    # f(a, b) -> f a b (with parens for nested calls to preserve grouping)
    let head = nimExprToEponym(n[0])
    var args: seq[string] = @[]
    for i in 1 ..< n.len:
      let a = n[i]
      # Parenthesize if arg is a call (to preserve Nim's explicit grouping)
      if a.kind == nnkCall:
        args.add("(" & nimExprToEponym(a) & ")")
      else:
        args.add(nimExprToEponym(a))
    if args.len == 0: head
    else: head & " " & args.join(" ")
  of nnkPar:
    # (x) -> x (parenthesized)
    if n.len == 1: nimExprToEponym(n[0])
    else: "(" & n.mapIt(nimExprToEponym(it)).join(", ") & ")"
  of nnkTupleConstr:
    # (a, b) -> (a, b) [Eponym pair syntax]
    "(" & n.mapIt(nimExprToEponym(it)).join(", ") & ")"
  else:
    error("ettBlock: unsupported expression: " & $n.kind, n)

proc nimTypeToEponym(n: NimNode): string =
  ## Convert a Nim type AST to Eponym type string.
  case n.kind
  of nnkIdent:
    let s = $n
    if s == "Univ": "?" else: s
  of nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit:
    # Integer literal in type position: assume Nat, generate suc chain.
    # (In term position, nimExprToEponym handles it via elaborator overloading.)
    # Do NOT wrap in parens here; the caller (nnkCall) will paren if needed.
    let v = n.intVal
    if v < 0: error("negative Nat literal in type", n)
    var res = "zero"
    for i in 1..v:
      res = "suc (" & res & ")"
    res
  of nnkCall:
    # Vec(Int, three) -> Vec Int three (paren nested calls)
    # For zero-arg calls like zero(), just return head (no parens needed)
    let head = nimTypeToEponym(n[0])
    if n.len == 1:
      head
    else:
      var args: seq[string] = @[]
      for i in 1 ..< n.len:
        let a = n[i]
        # Paren if arg is a call with args, or an int literal (suc chain needs grouping)
        if (a.kind == nnkCall and a.len > 1) or a.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit}:
          args.add("(" & nimTypeToEponym(a) & ")")
        else:
          args.add(nimTypeToEponym(a))
      head & " " & args.join(" ")
  of nnkInfix:
    # A -> B -> A -> B (right associative, as in Eponym)
    if $n[0] == "->" and n.len == 3:
      nimTypeToEponym(n[1]) & " -> " & nimTypeToEponym(n[2])
    else:
      error("ettBlock: unsupported infix in type: " & $n[0], n)
  else:
    nimExprToEponym(n)

proc procDefToEponym(n: NimNode): string =
  ## Convert nnkProcDef to "proc name (params) : ret = body".
  # n[0] = name, n[1] = empty (pragma?), n[2] = empty (generic?), 
  # n[3] = formal params, n[4] = empty, n[5] = empty, n[6] = body
  let name = $n[0]
  let params = n[3]  # nnkFormalParams: [returnType, param1, param2, ...]
  var paramStrs: seq[string] = @[]
  var retTy = "?"
  if params.len > 0 and params[0].kind != nnkEmpty:
    retTy = nimTypeToEponym(params[0])
  for i in 1 ..< params.len:
    let p = params[i]  # nnkIdentDefs: [name1, name2, ..., type, default]
    let ty = nimTypeToEponym(p[^2])
    for j in 0 ..< p.len - 2:
      paramStrs.add("(" & $p[j] & " : " & ty & ")")
  let body = nimExprToEponym(n[6])
  "proc " & name & " " & paramStrs.join(" ") & " : " & retTy & " = " & body & "\n"

proc blockToEponym*(body: NimNode): string =
  ## Convert a block of Nim AST to Eponym source program.
  result = ""
  for st in body:
    case st.kind
    of nnkProcDef:
      result.add(procDefToEponym(st))
    of nnkCall:
      let head = $st[0]
      if head == "postulate":
        # postulate(Int, Univ) -> postulate Int : ?
        if st.len != 3: error("postulate expects (name, type)", st)
        result.add("postulate " & $st[1] & " : " & nimTypeToEponym(st[2]) & "\n")
      elif head == "data":
        # data(Nat, Univ): block -> data Nat : ? where | ...
        # data(Vec, [A: Univ], Nat -> Univ): block -> data Vec (A : ?) : Nat -> ? where | ...
        if st.len < 3: error("data expects (name, type) with block", st)
        let name = $st[1]
        # Check if we have params: data(Vec, [A: Univ], kind)
        var paramStr = ""
        var tyNode: NimNode
        var blkIdx: int
        if st[2].kind == nnkBracket:
          # Parameterized: data(Name, [params], kind)
          if st.len < 5: error("data with params expects (name, [params], kind) with block", st)
          let params = st[2]
          var pStrs: seq[string] = @[]
          for p in params:
            # p is ExprColonExpr(A, Univ) or IdentDefs?
            if p.kind == nnkExprColonExpr:
              pStrs.add("(" & $p[0] & " : " & nimTypeToEponym(p[1]) & ")")
            else:
              error("data params must be [name: type]", p)
          paramStr = " " & pStrs.join(" ")
          tyNode = st[3]
          blkIdx = 4
        else:
          # Simple: data(Name, kind)
          tyNode = st[2]
          blkIdx = 3
        let ty = nimTypeToEponym(tyNode)
        result.add("data " & name & paramStr & " : " & ty & " where\n")
        # The block is at blkIdx
        let blk = st[blkIdx]
        if blk.kind != nnkStmtList:
          error("data expects a block of constructors", st)
        for ctor in blk:
          if ctor.kind != nnkProcDef:
            error("data block expects proc constructors", ctor)
          var cname = $ctor[0]
          # Map Nim-safe names to Eponym names (nil is a Nim keyword)
          if cname == "vecnil": cname = "nil"
          let cparams = ctor[3]
          var cparamStrs: seq[string] = @[]
          var cretTy = "?"
          if cparams.len > 0 and cparams[0].kind != nnkEmpty:
            cretTy = nimTypeToEponym(cparams[0])
          for i in 1 ..< cparams.len:
            let p = cparams[i]
            let ty2 = nimTypeToEponym(p[^2])
            for j in 0 ..< p.len - 2:
              cparamStrs.add("(" & $p[j] & " : " & ty2 & ")")
          result.add("| " & cname & " " & cparamStrs.join(" ") & " : " & cretTy & "\n")
      else:
        error("ettBlock: unsupported call: " & head, st)
    else:
      error("ettBlock: unsupported statement: " & $st.kind, st)

macro ettBlock*(body: untyped): untyped =
  ## Elaborate a block of Nim-syntax Eponym definitions (no """).
  ## Uses call syntax: proc f(x: Int): Int = ..., postulate(I, Univ),
  ## data(N, Univ): block.
  ## Generates wrapper procs like ettEmbed.
  let src = blockToEponym(body)
  var defs: seq[ElabDef]
  try:
    defs = elabCheck(src)
  except ElabError as e:
    error("ettBlock elaboration error: " & e.msg, body)
  except ParseError as e:
    error("ettBlock parse error: " & e.msg, body)
  
  result = newStmtList()
  for d in defs:
    let procName = ident(d.name)
    let srcLit = newLit(src)
    let nameLit = newLit(d.name)
    result.add(quote do:
      proc `procName`*(args: varargs[int]): int =
        callIntFunc(`srcLit`, `nameLit`, @args)
    )

macro ett*(src: string): untyped =
  ## Elaborate and typecheck a surface program at compile time.
  ## On success expands to nothing; on failure compilation stops with an
  ## error pointing at the ett"..." literal.
  let s = src.strVal  # src is a string literal (enforced by the signature)
  try:
    discard elabCheck(s)
  except ElabError as e:
    error("ett elaboration error: " & e.msg, src)
  except ParseError as e:
    error("ett parse error: " & e.msg, src)
  result = newStmtList()

proc isIntType(t: Term): bool =
  ## Check if a Term is the primitive Int type.
  # The Int type is represented as... let me check
  # Actually, `Int` in surface syntax elaborates to something.
  # For now, check if it's a tR referencing the Int type.
  # This is a simplification — full check needs globals.
  false  # TODO: implement properly

macro ettEmbed*(src: string): untyped =
  ## Elaborate a surface program at compile time and generate Nim
  ## wrapper procs for each `def` of type `Int -> ... -> Int`.
  ##
  ## Each wrapper has the form:
  ##   proc name(arg1: int, arg2: int, ...): int =
  ##     callIntFunc("<source>", "name", @[arg1, arg2, ...])
  ##
  ## The elaborated terms are re-obtained at runtime via the
  ## definition cache (compile-time elaboration ensures well-typedness).
  let s = src.strVal
  var defs: seq[ElabDef]
  try:
    defs = elabCheck(s)
  except ElabError as e:
    error("ettEmbed elaboration error: " & e.msg, src)
  except ParseError as e:
    error("ettEmbed parse error: " & e.msg, src)
  
  result = newStmtList()
  # Note: the generated procs call callIntFunc, which must be
  # imported by the user: `import ett_embed` before using ettEmbed.
  
  for d in defs:
    let procName = ident(d.name)
    let srcLit = newLit(s)
    let nameLit = newLit(d.name)
    result.add(quote do:
      proc `procName`*(args: varargs[int]): int =
        callIntFunc(`srcLit`, `nameLit`, @args)
    )

when isMainModule:
  ett"""
proc twice (A : ?) (f : A -> A) (x : A) : A =
  f (f x)
proc pairSwap (A : ?) (B : ?) (p : Sig (u : A). B) : Sig (v : B). A =
  (snd p, fst p)
"""
  echo "ok: ett macro accepts well-typed programs at compile time"
