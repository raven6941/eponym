## Experiment 2: the `ett` macro -- compile-time elaboration and checking.
##
## Deliberately thin (see decisions.org on Nimony/Nim 3): the parser and
## elaborator are plain Nim code in parse_surf and elab; the macro only feeds
## them a string literal and turns failures into compiler errors. No NimNode
## inspection, no hygiene tricks -- nothing that ties us to Nim 2's macro API.

import macros
import std/tables
import elab
import eponym_embed  # runtime wrapper helpers and adapter-shape validation
import eponym_init # opaque Value conversion helpers
import parse_surf
import os  # issue #131: parentDir of the eponymBlock call site
import strutils
import sequtils
import sets

# --- eponymBlock: Nim-block syntax (no """) ---------------------------------
# Converts a block of (valid Nim) AST to Eponym source, elaborates it,
# and generates wrapper procs. Uses call syntax:
#   proc add42(n: Int): Int = addInt(n, 42)
#   postulate(Int, Univ)
#   data(Nat, Univ):
#     proc zero(): Nat
#     proc suc(n: Nat): Nat

proc callerDir(body: NimNode): string =
  ## Directory of the Nim file containing the macro call (Issue #131).
  ## instantiationInfo() is unreliable inside macros, so parse it out of
  ## lineInfo, which has the form /abs/path/file.nim(line, col).
  let li = lineInfo(body)
  let p = li.rfind('(')
  if p < 0:
    error("eponymBlock: cannot determine calling file", body)
  parentDir(li[0 ..< p])

proc binderName(n: NimNode): string =
  ## Param/binder name, unwrapping a quantity pragma: `ch {.linear.}` -> "ch".
  if n.kind == nnkPragmaExpr: $n[0]
  else: $n

proc qtyPrefix(n: NimNode): string =
  ## Eponym quantity prefix from a Nim param pragma:
  ## `ch {.linear.}` -> "1 ", `ch {.erased.}` -> "0 ",
  ## `ch {.qvar(q).}` -> "q " (quantity *variable* binder, issue #151/#66).
  if n.kind == nnkPragmaExpr and n.len == 2 and n[1].kind == nnkPragma:
    for pr in n[1]:
      case pr.kind
      of nnkIdent:
        case $pr
        of "linear": return "1 "
        of "erased": return "0 "
        else: error("eponymBlock: unknown quantity pragma: " & $pr &
                    " (want linear/erased or qvar(q))", pr)
      of nnkCall:
        if pr[0].kind == nnkIdent and $pr[0] == "qvar" and pr.len == 2 and
           pr[1].kind == nnkIdent:
          return $pr[1] & " "
        error("eponymBlock: unsupported param pragma (want linear/erased or qvar(q))", pr)
      else:
        error("eponymBlock: unsupported param pragma", pr)
    return ""
  return ""

proc nimExprToEponym(n: NimNode): string
proc nimTypeToEponym(n: NimNode): string

proc ifExprToEponym(n: NimNode): string =
  var branches: seq[(NimNode, NimNode)] = @[]
  var elseBranch: NimNode = nil
  for branch in n:
    case branch.kind
    of nnkElifExpr, nnkElifBranch:
      if branch.len != 2:
        error("eponymBlock: if branch must have one condition and body", branch)
      branches.add((branch[0], branch[1]))
    of nnkElseExpr, nnkElse:
      if branch.len != 1:
        error("eponymBlock: else branch must have one body", branch)
      elseBranch = branch[0]
    else:
      error("eponymBlock: unsupported if branch " & $branch.kind, branch)
  if branches.len == 0 or elseBranch.isNil:
    error("eponymBlock: pure if expression requires a condition and an else branch", n)
  proc branchExpr(branch: NimNode): NimNode =
    if branch.kind == nnkStmtList:
      if branch.len != 1:
        error("eponymBlock: if branch must be one expression", branch)
      return branch[0]
    branch
  if elseBranch.kind == nnkStmtList:
    if elseBranch.len != 1:
      error("eponymBlock: else branch must be one expression", elseBranch)
    elseBranch = elseBranch[0]
  # Eponym applications are strict, while Nim conditionals evaluate only the
  # selected branch. Pass each branch as a unit thunk so a postulate (or any
  # other runtime-bound operation) in the unselected branch is not evaluated.
  var fallback = "(lam (_ : 1). " & nimExprToEponym(elseBranch) & ")"
  for i in countdown(branches.high, 0):
    let (condition, body) = branches[i]
    let yesBranch = "(lam (_ : 1). " & nimExprToEponym(branchExpr(body)) & ")"
    fallback = "ifThenElse (" & nimExprToEponym(condition) & ") " &
      yesBranch & " (" & fallback & ")"
  "(" & fallback & ") <>"

proc nimCommandLamToEponym(n: NimNode): string =
  ## Convert Nim's command-form untyped lambda (`lam x. body`) to Eponym
  ## syntax. Nim represents a nested chain such as `lam x. lam y. body`
  ## as `Command(lam, Command(DotExpr(x, lam), DotExpr(y, body)))`.
  if n.kind != nnkCommand or n.len != 2 or
     n[0].kind != nnkIdent or $n[0] != "lam":
    error("eponymBlock: unsupported command-form lambda", n)
  let arg = n[1]
  if arg.kind == nnkDotExpr and arg.len == 2:
    return "lam " & nimExprToEponym(arg[0]) & ". " &
           nimExprToEponym(arg[1])
  if arg.kind == nnkCommand and arg.len == 2 and
     arg[0].kind == nnkDotExpr and arg[0].len == 2 and
     arg[0][1].kind == nnkIdent and $arg[0][1] == "lam":
    var nested = newNimNode(nnkCommand)
    nested.add(ident("lam"))
    nested.add(arg[1])
    # A command-form typed binder such as `(n : Nat)` is represented as a
    # tuple/colon AST, not an identifier. Reuse the expression converter so
    # typed binders survive in nested command lambdas.
    return "lam " & nimExprToEponym(arg[0][0]) & ". " &
           nimCommandLamToEponym(nested)
  error("eponymBlock: unsupported command-form lambda", n)

proc nimCommandToEponym(n: NimNode): string =
  ## Nim's command-call syntax (`suc n`) is also nnkCommand. Treat ordinary
  ## commands as applications and reserve the special parser for `lam`.
  ## Nim nests whitespace-separated command arguments in child Command
  ## nodes; flatten those arguments instead of grouping them as one term.
  if n.len == 0: error("eponymBlock: empty command expression", n)
  if n[0].kind == nnkIdent and $n[0] == "lam":
    return nimCommandLamToEponym(n)
  var args: seq[string] = @[]
  proc appendArg(a: NimNode) =
    if a.kind == nnkCommand and a.len > 0 and
       not (a[0].kind == nnkIdent and $a[0] == "lam"):
      appendArg(a[0])
      for j in 1 ..< a.len:
        appendArg(a[j])
    elif a.kind == nnkCommand:
      args.add("(" & nimCommandLamToEponym(a) & ")")
    elif a.kind in {nnkCall, nnkObjConstr}:
      args.add("(" & nimExprToEponym(a) & ")")
    else:
      args.add(nimExprToEponym(a))
  for i in 1 ..< n.len:
    appendArg(n[i])
  nimExprToEponym(n[0]) & " " & args.join(" ")

proc nimExprToEponym(n: NimNode): string =
  ## Convert a Nim expression AST to Eponym source string.
  case n.kind
  of nnkIdent:
    var s = $n
    # Map Nim-safe names to Eponym names
    if s == "vecnil": s = "nil"
    if s == "unitv": s = "<>"   # issue #151: `<>` is not valid Nim syntax
    if s == "unitTy": s = "1"   # issue #151: the unit *type* (QTT)
    if s == "emptyTy": s = "O"  # issue #151: the empty type
    if s == "Univ": "Type 0"
    elif s == "_": "?"
    else: s
  of nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit:
    # In eponymBlock, integer literals are passed through verbatim and
    # overloaded by the elaborator (checkTm pkInt: Nat when the expected
    # type is Nat, primitive Int when it is Int) -- the same semantics
    # as string syntax. This also resolves Issue #8: nested literals in
    # eponymBlock bodies (e.g. cons(Int, 2, a, ...), eConst 3) now elaborate
    # per their expected type instead of always becoming Nat suc-chains.
    # Exception: 1 lexes as the *unit type* in surface syntax (QTT), so use
    # the parser's unambiguous integer spelling `01`. Expected-type
    # overloading then selects Nat or Int, just as it does for other literals.
    let v = n.intVal
    if v < 0: error("negative integer literal", n)
    if v == 1: "01" else: $v
  of nnkStmtList:
    # Proc body: convert let-statements to nested let...in, final expr is body
    if n.len == 0: error("eponymBlock: empty proc body", n)
    # Collect lets and final expression
    var lets: seq[(string, string, string)] = @[]  # (name, type-or-"", value)
    var finalExpr: NimNode = nil
    for stmt in n:
      if stmt.kind == nnkLetSection:
        for def in stmt:
          # nnkIdentDefs: [name, type, value]; the type may be Empty
          # (issue #151: typed lets keep their annotation)
          let name = $def[0]
          var tyAnn = ""
          if def[1].kind != nnkEmpty:
            tyAnn = " : " & nimTypeToEponym(def[1])
          let val = nimExprToEponym(def[2])
          lets.add((name, tyAnn, val))
      else:
        # Final expression (or single expression)
        if finalExpr != nil:
          error("eponymBlock: proc body must be lets followed by single expr", n)
        finalExpr = stmt
    if finalExpr == nil:
      error("eponymBlock: proc body must end with expression", n)
    var res = nimExprToEponym(finalExpr)
    # Wrap in let...in (innermost first, so reverse)
    for i in countdown(lets.len - 1, 0):
      let (nm, ty, vl) = lets[i]
      res = "let " & nm & ty & " = " & vl & " in " & res
    res
  of nnkObjConstr:
    # Pi(...)/Sig(...) type expressions in body position: Nim parses
    # them as object constructors, not calls. They are types, so route
    # through the type converter.
    nimTypeToEponym(n)
  of nnkCall:
    # byTac(refl) -> by refl (surface tactic term; smoke test 14, issue #151)
    if n[0].kind == nnkIdent and $n[0] == "byTac":
      if n.len != 2:
        error("byTac expects (tacticName)", n)
      let t = n[1]
      if t.kind == nnkIdent: return "by " & $t
      elif t.kind == nnkStrLit: return "by " & t.strVal
      else: error("byTac expects a tactic name (ident or string)", n)
    # Pi/Sig in expression position, positional form Sig(name, Dom, Body):
    # Nim parses it as a call, not an obj-constr. Route to the type converter.
    if n[0].kind == nnkIdent and $n[0] in ["Pi", "Sig"]:
      return nimTypeToEponym(n)
    # lam(x, T, body) -> lam (x : T). body (surface lambdas in eponymBlock bodies)
    if n[0].kind == nnkIdent and $n[0] == "lam":
      if n.len != 4 or n[1].kind notin {nnkIdent, nnkPragmaExpr}:
        error("lam expects (binder, type, body)", n)
      return "lam (" & qtyPrefix(n[1]) & binderName(n[1]) & " : " &
             nimTypeToEponym(n[2]) & "). " & nimExprToEponym(n[3])
    # f(a, b) -> f a b (with parens for nested calls to preserve grouping)
    let head = nimExprToEponym(n[0])
    var args: seq[string] = @[]
    for i in 1 ..< n.len:
      let a = n[i]
      # Parenthesize if arg is a call or obj-constr (Pi/Sig type args
      # parse as nnkObjConstr in expression position and need grouping too)
      if a.kind in {nnkCall, nnkObjConstr, nnkCommand}:
        args.add("(" & nimExprToEponym(a) & ")")
      else:
        args.add(nimExprToEponym(a))
    if args.len == 0: head
    else: head & " " & args.join(" ")
  of nnkPar:
    # (x) -> x (parenthesized)
    if n.len == 1: nimExprToEponym(n[0])
    else: "(" & n.mapIt(nimExprToEponym(it)).join(", ") & ")"
  of nnkCommand:
    nimCommandToEponym(n)
  of nnkBracketExpr:
    if n.len < 2:
      error("eponymBlock: bracket application needs explicit arguments", n)
    var parts = @[nimExprToEponym(n[0])]
    for i in 1 ..< n.len:
      let arg = n[i]
      let value = nimExprToEponym(arg)
      if arg.kind in {nnkCall, nnkCommand, nnkObjConstr, nnkInfix, nnkPrefix}:
        parts.add("(" & value & ")")
      else:
        parts.add(value)
    parts.join(" ")
  of nnkInfix:
    let prim = case $n[0]
      of "+": "addInt"
      of "-": "subInt"
      of "*": "mulInt"
      else: error("eponymBlock: unsupported pure operator '" & $n[0] & "'",
                  n[0])
    prim & " (" & nimExprToEponym(n[1]) & ") (" &
      nimExprToEponym(n[2]) & ")"
  of nnkPrefix:
    if $n[0] == "-":
      "subInt 0 (" & nimExprToEponym(n[1]) & ")"
    else:
      error("eponymBlock: unsupported pure prefix operator '" & $n[0] & "'",
            n[0])
  of nnkIfExpr, nnkIfStmt:
    ifExprToEponym(n)
  of nnkDotExpr:
    # p.x -> (p).x (record projection, issue #37; the surface parser
    # resolves it against the record table at elaboration time).
    # The LHS is parenthesized: in `mkPt(x, y).x` the dot must not
    # rebind to `y`.
    "(" & nimExprToEponym(n[0]) & ")." & nimExprToEponym(n[1])
  of nnkTupleConstr:
    # (t : T) ascription (Nim parses it as a 1-tuple of ExprColonExpr);
    # (a, b) -> (a, b) [Eponym pair syntax]
    if n.len == 1 and n[0].kind == nnkExprColonExpr and n[0].len == 2:
      "(" & nimExprToEponym(n[0][0]) & " : " & nimTypeToEponym(n[0][1]) & ")"
    else:
      "(" & n.mapIt(nimExprToEponym(it)).join(", ") & ")"
  else:
    error("eponymBlock: unsupported expression: " & $n.kind, n)

proc piSigToEponym(n: NimNode): string
  ## Convert Pi(...)/Sig(...) (nnkCall or nnkObjConstr) to Eponym.
  ## Pi(x: A, y {.linear.}: B, C) -> Pi (x : A). Pi (1 y : B). C
  ## Sig(x: A, B) -> Sig (x : A). B ; Sig(A, B) -> Sig (_ : A). B
  ## Note: Nim parses `Pi(x: A, ...)` with named binders as nnkObjConstr,
  ## not nnkCall, so both shapes must be handled.

proc nimTypeToEponym(n: NimNode): string =
  ## Convert a Nim type AST to Eponym type string.
  case n.kind
  of nnkIdent:
    var s = $n
    # Map Nim-safe names to Eponym names (issue #144: same mapping as
    # expressions -- `nil` is a Nim keyword, so constructor references in
    # types must go through `vecnil` too)
    if s == "vecnil": s = "nil"
    if s == "unitv": s = "<>"   # issue #151: `<>` is not valid Nim syntax
    if s == "unitTy": s = "1"   # issue #151: the unit *type* (QTT)
    if s == "emptyTy": s = "O"  # issue #151: the empty type
    if s == "Univ": "Type 0" else: s
  of nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit:
    # Integer literal in type position: passed through verbatim; the
    # elaborator overloads it against the expected type (Nat or Int),
    # exactly as in string syntax (Issues #8, #115).
    # Exception: 1 lexes as the *unit type* in surface syntax (QTT), so
    # the Nat literal one is spelled `suc zero` (as in string syntax).
    let v = n.intVal
    if v < 0: error("negative integer literal in type", n)
    if v == 1: "(suc zero)" else: $v
  of nnkBracketExpr:
    if n.len < 2:
      error("eponymBlock: bracket type application needs explicit arguments", n)
    let head = nimTypeToEponym(n[0])
    var args: seq[string] = @[]
    for i in 1 ..< n.len:
      let a = n[i]
      if (a.kind == nnkCall and a.len > 1) or a.kind == nnkObjConstr or
          a.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                     nnkInt64Lit}:
        args.add("(" & nimTypeToEponym(a) & ")")
      else:
        args.add(nimTypeToEponym(a))
    head & " " & args.join(" ")
  of nnkProcTy:
    if n.len != 2 or n[0].kind != nnkFormalParams or n[0].len != 2 or
        n[0][1].kind != nnkIdentDefs or n[0][1].len != 3:
      error("runtime proc types currently require exactly one named argument", n)
    let argName = if n[0][1][0].kind == nnkEmpty: "callbackArg" else: $n[0][1][0]
    "Pi (" & argName & " : " & nimTypeToEponym(n[0][1][^2]) & "). " &
      nimTypeToEponym(n[0][0])
  of nnkCall:
    # Tactic term in type position (issue #151): byTac(refl) -> by refl.
    if n[0].kind == nnkIdent and $n[0] == "byTac":
      return nimExprToEponym(n)
    # Vec(Int, three) -> Vec Int three (paren nested calls)
    # For zero-arg calls like zero(), just return head (no parens needed)
    if n[0].kind == nnkIdent and $n[0] in ["Pi", "Sig"]:
      return piSigToEponym(n)
    if n[0].kind == nnkIdent and $n[0] == "lam":
      # lam(x, T, body) -> lam (x : T). body (continuations in types)
      if n.len != 4 or n[1].kind notin {nnkIdent, nnkPragmaExpr}:
        error("lam expects (binder, type, body)", n)
      return "lam (" & qtyPrefix(n[1]) & binderName(n[1]) & " : " &
             nimTypeToEponym(n[2]) & "). " & nimTypeToEponym(n[3])
    let head = nimTypeToEponym(n[0])
    if n.len == 1:
      head
    else:
      var args: seq[string] = @[]
      for i in 1 ..< n.len:
        let a = n[i]
        # Paren if arg is a call with args, an obj-constr (Pi/Sig type args
        # parse as nnkObjConstr and need grouping too), or an int literal
        # (suc chain needs grouping)
        if (a.kind == nnkCall and a.len > 1) or a.kind == nnkObjConstr or a.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit}:
          args.add("(" & nimTypeToEponym(a) & ")")
        else:
          args.add(nimTypeToEponym(a))
      head & " " & args.join(" ")
  of nnkObjConstr:
    # Nim parses `Pi(x: A, y {.linear.}: B, C)` (named binders) as an object
    # constructor, not a call. Only Pi/Sig are meaningful here.
    if n[0].kind == nnkIdent and $n[0] in ["Pi", "Sig"]:
      return piSigToEponym(n)
    error("eponymBlock: unsupported object construction in type: " & $n[0], n)
  of nnkInfix:
    # A -> B -> A -> B (right associative, as in Eponym)
    if $n[0] == "->" and n.len == 3:
      nimTypeToEponym(n[1]) & " -> " & nimTypeToEponym(n[2])
    else:
      error("eponymBlock: unsupported infix in type: " & $n[0], n)
  of nnkPar:
    # Preserve explicit grouping: (A -> B) -> C must not flatten to
    # A -> B -> C, and (Pi (n : Nat). ...) -> ... must not let the Pi body
    # swallow the rest of the arrow chain (issue #151: the natElim motive
    # method needs those parens).
    if n.len == 1: "(" & nimTypeToEponym(n[0]) & ")"
    else: error("eponymBlock: unexpected parenthesized form in type", n)
  else:
    nimExprToEponym(n)

proc piSigToEponym(n: NimNode): string =
  let isPi = $n[0] == "Pi"
  if n.len < 3: error($n[0] & " expects binders and a body", n)
  # Sig in Call form (positional args, no colons): Sig(name, Dom, Body).
  if not isPi and n.kind == nnkCall:
    if n.len == 4 and n[1].kind == nnkIdent:
      return "Sig (" & $n[1] & " : " & nimTypeToEponym(n[2]) & "). " & nimTypeToEponym(n[3])
    elif n.len == 3:
      return "Sig (_ : " & nimTypeToEponym(n[1]) & "). " & nimTypeToEponym(n[2])
    else:
      error("Sig expects (binder, dom, body) or (dom, body)", n)
  var parts: seq[string] = @[]
  for i in 1 ..< n.len - 1:
    let b = n[i]
    var q, nm, dom: string
    if b.kind == nnkTableConstr:
      # {A : T, ...} -> implicit binders (Pi only). Each pair: name : type.
      if not isPi: error("implicit binders only meaningful in Pi", b)
      for pair in b:
        if pair.kind != nnkExprColonExpr or pair.len != 2 or pair[0].kind != nnkIdent:
          error("implicit binder must have form {name : type}", b)
        parts.add("Pi {" & $pair[0] & " : " & nimTypeToEponym(pair[1]) & "}. ")
      continue
    if b.kind == nnkExprColonExpr and b.len == 2:
      q = qtyPrefix(b[0])
      nm = binderName(b[0])
      dom = nimTypeToEponym(b[1])
    elif not isPi:
      # Sig(A, B): anonymous binder -> Sig (_ : A). B
      q = ""; nm = "_"; dom = nimTypeToEponym(b)
    else:
      error("Pi binder must have form name: type", b)
    if isPi:
      parts.add("Pi (" & q & nm & " : " & dom & "). ")
    else:
      parts.add("Sig (" & q & nm & " : " & dom & "). ")
  parts.join("") & nimTypeToEponym(n[^1])

proc patToEponym(n: NimNode): string =
  ## Clause patterns are surface *atoms*; constructor applications need
  ## parens in surface syntax (`(suc m)`), so wrap calls (issue #151).
  case n.kind
  of nnkIdent:
    if $n == "_": "_" else: nimExprToEponym(n)
  of nnkCall:
    let s = nimExprToEponym(n)
    if n.len > 1: "(" & s & ")" else: s
  of nnkPar:
    if n.len == 1 and n[0].kind == nnkCall: "(" & nimExprToEponym(n[0]) & ")"
    else: nimExprToEponym(n)
  else:
    nimExprToEponym(n)

proc procDefToEponym(n: NimNode): string =
  ## Convert nnkProcDef to "proc name (generic binders) (params) : ret = body".
  # n[0] = name, n[1] = empty (pragma?), n[2] = generic params,
  # n[3] = formal params, n[4] = empty, n[5] = empty, n[6] = body
  let name = $n[0]
  let params = n[3]  # nnkFormalParams: [returnType, param1, param2, ...]
  var genericBinders: seq[string] = @[]
  if n[2].kind != nnkEmpty:
    for genericParam in n[2]:
      if genericParam.kind != nnkIdentDefs or
          genericParam[^2].kind == nnkEmpty:
        error("eponymBlock: explicit generic parameters need Eponym type annotations", genericParam)
      let ty = nimTypeToEponym(genericParam[^2])
      for i in 0 ..< genericParam.len - 2:
        genericBinders.add("(" & binderName(genericParam[i]) & " : " & ty & ")")
  var paramStrs: seq[string] = @[]
  var retTy = "Type 0"
  if params.len > 0 and params[0].kind != nnkEmpty:
    retTy = nimTypeToEponym(params[0])
  for i in 1 ..< params.len:
    let p = params[i]  # nnkIdentDefs: [name1, name2, ..., type, default]
    let ty = nimTypeToEponym(p[^2])
    for j in 0 ..< p.len - 2:
      let q = qtyPrefix(p[j])
      paramStrs.add("(" & q & binderName(p[j]) & " : " & ty & ")")
  let body = nimExprToEponym(n[6])
  let genericStr = if genericBinders.len == 0: ""
                   else: " " & genericBinders.join(" ")
  "proc " & name & genericStr & " " & paramStrs.join(" ") & " : " & retTy &
    " = " & body & "\n"

proc defCallToEponym(st: NimNode): string =
  ## def(isZero, Nat -> Bool):
  ##   clause([zero], true)
  ##   clause([suc(n)], false)
  ## -> def isZero : Nat -> Bool / | zero = true / | (suc n) = false
  ## (issue #151: clause-style definitions embedded; issue #42: reused
  ## for defs inside a mutual block).
  if st.len < 4 or st[1].kind != nnkIdent:
    error("def expects (name, type) with a block of clause([pats], rhs)", st)
  result = "def " & $st[1] & " : " & nimTypeToEponym(st[2]) & "\n"
  let blk = st[st.len - 1]
  if blk.kind != nnkStmtList:
    error("def expects a block of clause([pats], rhs) statements", st)
  for c in blk:
    if c.kind != nnkCall or c[0].kind != nnkIdent or $c[0] != "clause":
      error("def block expects clause([pattern, ...], rhs) statements", c)
    if c.len != 3 or c[1].kind != nnkBracket:
      error("clause expects ([pattern, ...], rhs)", c)
    var pats: seq[string] = @[]
    for p in c[1]: pats.add(patToEponym(p))
    result.add("| " & pats.join(" ") & " = " & nimExprToEponym(c[2]) & "\n")

proc blockToEponym*(body: NimNode): string =
  ## Convert a block of Nim AST to Eponym source program.
  result = ""
  for st in body:
    case st.kind
    of nnkProcDef:
      result.add(procDefToEponym(st))
    of nnkImportStmt:
      # Issue #131: import "../../lib/nat.ep" -> import "../../lib/nat.ep"
      # (Eponym source line). Paths resolve relative to the Nim file
      # containing the eponymBlock call (see the eponymBlock macro below).
      for p in st:
        if p.kind != nnkStrLit:
          error("eponymBlock: import expects a string path, e.g. import \"lib/nat.ep\"", p)
        result.add("import \"" & p.strVal & "\"\n")
    of nnkCall:
      let head = $st[0]
      if head == "postulate":
        # postulate(Int, Univ) -> postulate Int : Type 0
        if st.len != 3: error("postulate expects (name, type)", st)
        result.add("postulate " & $st[1] & " : " & nimTypeToEponym(st[2]) & "\n")
      elif head == "elim":
        # elim(boolElim, Pi(C: Bool -> Univ, ...)) -> elim boolElim : Pi ...
        # (issue #151: smoke tests 07/08 embedded)
        if st.len != 3 or st[1].kind != nnkIdent:
          error("elim expects (name, type)", st)
        result.add("elim " & $st[1] & " : " & nimTypeToEponym(st[2]) & "\n")
      elif head == "red":
        # red(boolElim(C, t, f, true), t) -> red boolElim C t f true = t
        # (issue #151: smoke tests 07/08 embedded)
        if st.len != 3:
          error("red expects (lhs, rhs)", st)
        result.add("red " & nimExprToEponym(st[1]) & " = " &
                   nimExprToEponym(st[2]) & "\n")
      elif head == "def":
        result.add(defCallToEponym(st))
      elif head == "mutual":
        # mutual:
        #   def(even, Nat -> Bool): clause([zero], true) ...
        #   def(odd, Nat -> Bool): ...
        # -> mutual / def even : ... / | ... / def odd : ... / | ...
        # (issue #42: mutual blocks embedded)
        if st.len != 2:
          error("mutual expects a block of def(name, type) groups", st)
        let mblk = st[1]
        if mblk.kind != nnkStmtList:
          error("mutual expects a block of def(name, type) groups", st)
        result.add("mutual\n")
        var ndefs = 0
        for d in mblk:
          if d.kind != nnkCall or d[0].kind != nnkIdent or $d[0] != "def":
            error("mutual block expects def(name, type) groups", d)
          result.add(defCallToEponym(d))
          inc ndefs
        if ndefs == 0:
          error("mutual needs at least one def group", st)
      elif head == "data":
        # data(Nat, Univ): block -> data Nat : Type 0 where | ...
        # data(Vec, [A: Univ], Nat -> Univ): block -> data Vec (A : Type 0) : Nat -> Type 0 where | ...
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
              let q = qtyPrefix(p[j])
              cparamStrs.add("(" & q & binderName(p[j]) & " : " & ty2 & ")")
          result.add("| " & cname & " " & cparamStrs.join(" ") & " : " & cretTy & "\n")
      elif head == "record":
        # record(Point): block -> record Point: | ...
        # block statements are field(name, Type) calls (issue #37)
        if st.len != 3 or st[1].kind != nnkIdent:
          error("record expects (name) with a block of field(name, type)", st)
        let name = $st[1]
        result.add("record " & name & ":\n")
        let blk = st[2]
        if blk.kind != nnkStmtList:
          error("record expects a block of field(name, type) statements", st)
        for f in blk:
          if f.kind != nnkCall or f[0].kind != nnkIdent or $f[0] != "field":
            error("record block expects field(name, type) statements", f)
          if f.len != 3 or f[1].kind != nnkIdent:
            error("field expects (name, type)", f)
          result.add("| " & $f[1] & " : " & nimTypeToEponym(f[2]) & "\n")
      elif head == "bindPostulate":
        # Host binding is consumed by eponymBlock after checking its Eponym
        # contract; it is not part of the Eponym source text.
        if st.len notin {3, 4, 5, 6, 7, 8, 9} or st[1].kind != nnkIdent:
          error("bindPostulate expects (postulateName, nimProcedure[, EponymType...])", st)
      elif head == "bindPostulateValue":
        # Deliberate raw runtime escape hatch; the Nim adapter owns codecs.
        if st.len != 3 or st[1].kind != nnkIdent:
          error("bindPostulateValue expects (postulateName, nimProcedure)", st)
      elif head == "bindPostulatePair":
        # Typed adapter for A1 -> ... -> An -> Sig(B, C).
        if st.len notin {6, 7, 8} or st[1].kind != nnkIdent:
          error("bindPostulatePair expects (name, nimProc, Argument[, Argument...], First, Second)", st)
        for i in 3 ..< st.len:
          if st[i].kind != nnkIdent:
            error("bindPostulatePair Eponym types must be identifiers", st[i])
      elif head == "bindPostulatePairTrusted":
        # Same codec as bindPostulatePair, with a trusted dependent index.
        if st.len notin {6, 7, 8} or st[1].kind != nnkIdent:
          error("bindPostulatePairTrusted expects (name, nimProc, Argument[, Argument...], First, Second)", st)
        for i in 3 ..< st.len:
          if st[i].kind != nnkIdent:
            error("bindPostulatePairTrusted Eponym types must be identifiers", st[i])
      elif head == "runtimeType":
        # Explicit opaque Nim/Eponym representation mapping, consumed by the
        # wrapper generator and never interpreted as an Eponym declaration.
        if st.len != 3 or st[1].kind != nnkIdent:
          error("runtimeType expects (EponymType, NimType)", st)
      elif head == "runtimeValue":
        # Request a raw Eponym Value wrapper for a checked definition,
        # typically for a host interpreter of reified data.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeValue expects (checkedDefinition)", st)
      else:
        error("eponymBlock: unsupported call: " & head, st)
    else:
      error("eponymBlock: unsupported statement: " & $st.kind, st)

type HostPostulateBinding = object
  postulateName: string
  implementation: NimNode
  eponymTypes: seq[string]
  pairResult: bool
  pairArgCount: int
  trustedPairIndex: bool
  rawValue: bool

type HostRuntimeType = object
  eponymName: string
  nimType: NimNode

proc mentionsName(node: NimNode, name: string): bool

type HostRecordField = object
  name: string
  eponymType: NimNode

type HostRecord = object
  name: string
  fields: seq[HostRecordField]
  hasDependentField: bool

proc hostRecords(body: NimNode): seq[HostRecord] =
  for st in body:
    if st.kind != nnkCall or st.len != 3 or st[0].kind != nnkIdent or
        $st[0] != "record" or st[1].kind != nnkIdent or
        st[2].kind != nnkStmtList:
      continue
    var record = HostRecord(name: $st[1])
    for field in st[2]:
      if field.kind != nnkCall or field.len != 3 or
          field[0].kind != nnkIdent or $field[0] != "field" or
          field[1].kind != nnkIdent:
        continue # blockToEponym reports malformed record fields
      let fieldType = field[2]
      for previous in record.fields:
        if mentionsName(fieldType, previous.name):
          record.hasDependentField = true
      record.fields.add(HostRecordField(name: $field[1],
                                         eponymType: fieldType))
    result.add(record)

proc findHostRecord(records: seq[HostRecord], name: string): int =
  for i, record in records:
    if record.name == name: return i
  -1

proc hostRuntimeTypes(body: NimNode): seq[HostRuntimeType] =
  var seen = initHashSet[string]()
  for st in body:
    if st.kind == nnkCall and st.len > 0 and st[0].kind == nnkIdent and
        $st[0] == "runtimeType":
      if st.len != 3 or st[1].kind != nnkIdent:
        error("runtimeType expects (EponymType, NimType)", st)
      let name = $st[1]
      if name in seen:
        error("duplicate runtimeType mapping for '" & name & "'", st)
      seen.incl(name)
      result.add(HostRuntimeType(eponymName: name, nimType: st[2]))

proc validateHostBoolCodec(globals: Globals) =
  if "Bool" notin globals:
    raise newException(ValueError, "Bool is not declared; import bool.ep")
  let boolId = globals["Bool"].tm.refId
  for constructorName in ["true", "false"]:
    if constructorName notin globals:
      raise newException(ValueError,
        "Bool constructor '" & constructorName & "' is not declared; import bool.ep")
    let constructor = globals[constructorName]
    if not constructor.isDataConstructor or constructor.ty.isNil or
        constructor.ty.kind != tR or constructor.ty.refId != boolId:
      raise newException(ValueError,
        "Bool codec requires '" & constructorName & "' to construct Bool")

proc hostPostulateBindings(body: NimNode): seq[HostPostulateBinding] =
  var seen = initHashSet[string]()
  for st in body:
    if st.kind == nnkCall and st.len > 0 and st[0].kind == nnkIdent and
        $st[0] in ["bindPostulate", "bindPostulateValue", "bindPostulatePair",
                   "bindPostulatePairTrusted"]:
      let rawValue = $st[0] == "bindPostulateValue"
      let pairResult = $st[0] in ["bindPostulatePair", "bindPostulatePairTrusted"]
      let trustedPairIndex = $st[0] == "bindPostulatePairTrusted"
      if pairResult:
        if st.len notin {6, 7, 8} or st[1].kind != nnkIdent:
          error($st[0] & " expects (name, nimProc, Argument[, Argument...], First, Second)", st)
      elif st.len notin {3, 4, 5, 6, 7, 8, 9} or st[1].kind != nnkIdent:
        error("bindPostulate expects (postulateName, nimProcedure[, EponymType...])", st)
      let name = $st[1]
      if name in seen:
        error("duplicate bindPostulate for '" & name & "'", st)
      seen.incl(name)
      var typeNames: seq[string] = @[]
      for i in 3 ..< st.len:
        if st[i].kind != nnkIdent:
          error("bindPostulate Eponym type mappings must be identifiers", st[i])
        typeNames.add($st[i])
      result.add(HostPostulateBinding(postulateName: name,
                                     implementation: st[2],
                                     eponymTypes: typeNames,
                                     pairResult: pairResult,
                                     pairArgCount: if pairResult:
                                       typeNames.len - 2 else: 0,
                                     trustedPairIndex: trustedPairIndex,
                                     rawValue: rawValue))

proc mentionsName(node: NimNode, name: string): bool =
  if node.kind in {nnkIdent, nnkSym} and $node == name:
    return true
  for child in node:
    if mentionsName(child, name):
      return true

proc bindingIsReferenced(body: NimNode, postulateName: string): bool =
  ## A binding is useful only if some checked proc body calls its postulate.
  ## This deliberately checks direct references; call-graph reachability is a
  ## separate question because any generated wrapper can be called by Nim.
  for st in body:
    if st.kind == nnkProcDef and st.len > 6 and
        mentionsName(st[6], postulateName):
      return true

proc isCheckedNatType(globals: Globals, typeName: string): bool =
  ## Classify Nat by the checked declaration's identity, not by its spelling.
  if "Nat" notin globals or typeName notin globals:
    return false
  let nat = globals["Nat"].tm
  let candidate = globals[typeName].tm
  not nat.isNil and not candidate.isNil and nat.kind == tR and
    candidate.kind == tR and nat.refId == candidate.refId

proc simpleRuntimeCodec(n: NimNode): string =
  if n.kind == nnkIdent:
    case $n
    of "Int": result = "int"
    of "Nat": result = "nat"
    of "Bool": result = "bool"
    else: result = ""

proc runtimeSigmaComponents(n: NimNode): tuple[first, second: NimNode] =
  ## Runtime tuples represent only non-dependent two-field Sig types. Reject
  ## dependent tails rather than erasing the first component from their type.
  if n.kind notin {nnkCall, nnkObjConstr} or n.len != 3 or
      n[0].kind != nnkIdent or
      $n[0] != "Sig":
    return
  if n[1].kind == nnkExprColonExpr:
    if n[1].len != 2 or n[1][0].kind != nnkIdent or
        mentionsName(n[2], $n[1][0]):
      return
    return (n[1][1], n[2])
  (n[1], n[2])

proc runtimeProcParts(n: NimNode): tuple[argType, resultType: NimNode] =
  if n.kind != nnkProcTy or n.len != 2 or n[0].kind != nnkFormalParams or
      n[0].len != 2 or n[0][1].kind != nnkIdentDefs or n[0][1].len != 3:
    return
  (n[0][1][^2], n[0][0])

proc hasClosurePragma(n: NimNode): bool =
  if n.kind == nnkProcTy and n.len == 2 and n[1].kind == nnkPragma:
    for pragma in n[1]:
      if pragma.kind in {nnkIdent, nnkSym} and $pragma == "closure":
        return true

proc runtimeNimType(n: NimNode, mappings: seq[HostRuntimeType],
                    records: seq[HostRecord]): NimNode =
  let procParts = runtimeProcParts(n)
  if not procParts.argType.isNil:
    if not hasClosurePragma(n): return nil
    let argType = runtimeNimType(procParts.argType, mappings, records)
    let resultType = runtimeNimType(procParts.resultType, mappings, records)
    if argType.isNil or resultType.isNil: return nil
    result = copyNimTree(n)
    result[0][0] = resultType
    result[0][1][^2] = argType
    return
  let sigma = runtimeSigmaComponents(n)
  if not sigma.first.isNil:
    let first = runtimeNimType(sigma.first, mappings, records)
    let second = runtimeNimType(sigma.second, mappings, records)
    if first.isNil or second.isNil: return nil
    result = newNimNode(nnkTupleConstr)
    result.add(first)
    result.add(second)
    return
  var head = n
  while head.kind in {nnkCall, nnkCommand, nnkBracketExpr} and head.len > 0:
    head = head[0]
  if head.kind == nnkIdent:
    let recordIndex = findHostRecord(records, $head)
    if recordIndex >= 0:
      let record = records[recordIndex]
      if record.hasDependentField or record.fields.len == 0:
        return nil
      for field in record.fields:
        if runtimeNimType(field.eponymType, mappings, records).isNil:
          return nil
      for mapping in mappings:
        if mapping.eponymName == $head:
          return mapping.nimType
      return nil
    case $head
    of "Int", "Nat": return ident("int")
    of "Bool": return ident("bool")
    else:
      for mapping in mappings:
        if mapping.eponymName == $head:
          return mapping.nimType
  nil

proc runtimeValueConverter(eponymType, nimType: NimNode,
                           toValue: bool,
                           records: seq[HostRecord]): NimNode =
  if simpleRuntimeCodec(eponymType) == "int":
    if toValue: return bindSym"intToValue"
    return bindSym"valueToInt"
  if simpleRuntimeCodec(eponymType) == "nat":
    if toValue: return bindSym"natToValue"
    return bindSym"valueToNat"
  if simpleRuntimeCodec(eponymType) == "bool":
    if toValue: return bindSym"boolToValue"
    return bindSym"valueToBool"
  if eponymType.kind == nnkCall and eponymType.len == 3 and
      eponymType[0].kind == nnkIdent and $eponymType[0] == "Sig":
    return nil # handled structurally by runtimeValueConversionExpr
  if eponymType.kind == nnkIdent and findHostRecord(records, $eponymType) >= 0:
    return nil # handled structurally by runtimeValueConversionExpr
  let generic = if toValue: bindSym"toHostValue" else: bindSym"valueToHost"
  newTree(nnkBracketExpr, generic, nimType)

proc runtimeValueConversionExpr(eponymType, nimType, value: NimNode,
                               toValue: bool,
                               mappings: seq[HostRuntimeType],
                               records: seq[HostRecord],
                               globals: NimNode): NimNode =
  let procParts = runtimeProcParts(eponymType)
  if not procParts.argType.isNil:
    let argNimType = runtimeNimType(procParts.argType, mappings, records)
    let resultNimType = runtimeNimType(procParts.resultType, mappings, records)
    if argNimType.isNil or resultNimType.isNil: return nil
    let argSym = genSym(nskParam, "runtimeCallbackArgument")
    if toValue:
      let decodedArg = runtimeValueConversionExpr(procParts.argType,
        argNimType, argSym, false, mappings, records, globals)
      if decodedArg.isNil: return nil
      let hostResult = newCall(value, decodedArg)
      let encodedResult = runtimeValueConversionExpr(procParts.resultType,
        resultNimType, hostResult, true, mappings, records, globals)
      if encodedResult.isNil: return nil
      let hostCallback = newProc(
        params = @[bindSym"Value",
          newIdentDefs(argSym, bindSym"Value", newEmptyNode())],
        body = newStmtList(encodedResult))
      return newCall(bindSym"vHostFunc", hostCallback)
    let encodedArg = runtimeValueConversionExpr(procParts.argType,
      argNimType, argSym, true, mappings, records, globals)
    if encodedArg.isNil: return nil
    let applied = newCall(bindSym"callRuntimeValue", value,
      newTree(nnkBracket, encodedArg))
    let decodedResult = runtimeValueConversionExpr(procParts.resultType,
      resultNimType, applied, false, mappings, records, globals)
    if decodedResult.isNil: return nil
    return newProc(
      params = @[resultNimType,
        newIdentDefs(argSym, argNimType, newEmptyNode())],
      body = newStmtList(decodedResult))
  let sigma = runtimeSigmaComponents(eponymType)
  if not sigma.first.isNil:
    if nimType.kind notin {nnkTupleConstr, nnkTupleTy} or nimType.len != 2:
      return nil
    if toValue:
      let first = runtimeValueConversionExpr(sigma.first, nimType[0],
        newTree(nnkBracketExpr, value, newLit(0)), true, mappings, records,
        globals)
      let second = runtimeValueConversionExpr(sigma.second, nimType[1],
        newTree(nnkBracketExpr, value, newLit(1)), true, mappings, records,
        globals)
      if first.isNil or second.isNil: return nil
      return newCall(bindSym"pairValue", first, second)
    let firstValue = newCall(bindSym"whnfFst", value)
    let secondValue = newCall(bindSym"whnfSnd", value)
    let first = runtimeValueConversionExpr(sigma.first, nimType[0],
      firstValue, false, mappings, records, globals)
    let second = runtimeValueConversionExpr(sigma.second, nimType[1],
      secondValue, false, mappings, records, globals)
    if first.isNil or second.isNil: return nil
    return newTree(nnkTupleConstr, first, second)
  if eponymType.kind == nnkIdent:
    let recordIndex = findHostRecord(records, $eponymType)
    if recordIndex >= 0:
      let record = records[recordIndex]
      if record.hasDependentField or record.fields.len == 0:
        return nil
      if toValue:
        var tail = newCall(bindSym"unitValue")
        for i in countdown(record.fields.high, 0):
          let field = record.fields[i]
          let fieldType = runtimeNimType(field.eponymType, mappings, records)
          if fieldType.isNil: return nil
          let fieldValue = newTree(nnkDotExpr, value, ident(field.name))
          let converted = runtimeValueConversionExpr(field.eponymType,
            fieldType, fieldValue, true, mappings, records, globals)
          if converted.isNil: return nil
          tail = newCall(bindSym"pairValue", converted, tail)
        return tail
      var current = value
      var fields = newNimNode(nnkObjConstr)
      fields.add(nimType)
      for field in record.fields:
        let fieldType = runtimeNimType(field.eponymType, mappings, records)
        if fieldType.isNil: return nil
        let converted = runtimeValueConversionExpr(field.eponymType,
          fieldType, newCall(bindSym"whnfFst", current), false,
          mappings, records, globals)
        if converted.isNil: return nil
        fields.add(newTree(nnkExprColonExpr, ident(field.name), converted))
        current = newCall(bindSym"whnfSnd", current)
      return fields
  let valueFn = runtimeValueConverter(eponymType, nimType, toValue, records)
  if valueFn.isNil: return nil
  if simpleRuntimeCodec(eponymType) == "bool" or
      (simpleRuntimeCodec(eponymType) == "nat" and not toValue):
    return newCall(valueFn, value, globals)
  newCall(valueFn, value)

proc genericRuntimeInfo(decl: NimNode,
                        mappings: seq[HostRuntimeType]): tuple[
    genericParams: NimNode, typeNames: seq[string],
    codecMappings: seq[HostRuntimeType], error: string] =
  result.genericParams = newEmptyNode()
  result.codecMappings = mappings
  if decl[2].kind == nnkEmpty:
    return
  result.genericParams = newNimNode(nnkGenericParams)
  for param in decl[2]:
    if param.kind != nnkIdentDefs or param[^2].kind == nnkEmpty or
        nimTypeToEponym(param[^2]) != "Type 0":
      result.error = "runtime wrappers currently support only type-level " &
        "generic binders annotated with Univ"
      return
    for i in 0 ..< param.len - 2:
      let name = $param[i]
      if name in result.typeNames:
        result.error = "duplicate generic runtime type parameter '" & name & "'"
        return
      if decl.len > 6 and not decl[6].isNil and mentionsName(decl[6], name):
        result.error = "generic type parameter '" & name &
          "' is used by the runtime body; an explicit runtime type " &
          "representation is required"
        return
      result.typeNames.add(name)
      result.genericParams.add(newIdentDefs(copyNimTree(param[i]),
        newEmptyNode(), newEmptyNode()))
      result.codecMappings.add(HostRuntimeType(eponymName: name,
        nimType: copyNimTree(param[i])))

proc bindingCall(binding: HostPostulateBinding, bindingsSym, globalsSym: NimNode,
                 mappings: seq[HostRuntimeType], records: seq[HostRecord],
                 checkedGlobals: Globals): NimNode =
  let nameLit = newLit(binding.postulateName)
  if binding.rawValue:
    return newCall(bindSym"bindHostValueNary", bindingsSym, globalsSym,
                   nameLit, binding.implementation)
  if binding.pairResult:
    let bindingForm = if binding.trustedPairIndex:
      "bindPostulatePairTrusted"
    else:
      "bindPostulatePair"
    let pairType = newCall(ident"Sig",
      ident(binding.eponymTypes[binding.pairArgCount]),
      ident(binding.eponymTypes[binding.pairArgCount + 1]))
    let pairNimType = runtimeNimType(pairType, mappings, records)
    if pairNimType.isNil:
      error(bindingForm & " needs runtime codecs for both pair fields")
    var runtimeArgs: seq[NimNode] = @[]
    var decodedArgs: seq[NimNode] = @[]
    for i in 0 ..< binding.pairArgCount:
      let eponymArgType = ident(binding.eponymTypes[i])
      let nimArgType = runtimeNimType(eponymArgType, mappings, records)
      if nimArgType.isNil:
        error(bindingForm & " needs a runtime codec for argument '" &
          binding.eponymTypes[i] & "'")
      let runtimeArg = genSym(nskParam, "runtimeArgument")
      runtimeArgs.add(runtimeArg)
      let decoded = runtimeValueConversionExpr(eponymArgType, nimArgType,
        runtimeArg, false, mappings, records, globalsSym)
      if decoded.isNil:
        error(bindingForm & " could not build an argument codec")
      decodedArgs.add(decoded)
    let hostResult = genSym(nskLet, "hostPairResult")
    let encodedResult = runtimeValueConversionExpr(pairType, pairNimType,
      hostResult, true, mappings, records, globalsSym)
    if encodedResult.isNil:
      error(bindingForm & " could not build a value codec")
    var adapterBody = newStmtList()
    var implementationCall = newCall(binding.implementation)
    for decodedArg in decodedArgs:
      implementationCall.add(decodedArg)
    adapterBody.add(newLetStmt(hostResult, implementationCall))
    adapterBody.add(encodedResult)
    var adapterValue = newCall(bindSym"vHostFunc",
      newProc(params = @[bindSym"Value",
        newIdentDefs(runtimeArgs[^1], bindSym"Value", newEmptyNode())],
        body = adapterBody))
    if binding.pairArgCount > 1:
      for i in countdown(binding.pairArgCount - 2, 0):
        let partialBody = newStmtList(adapterValue)
        let partialProc = newProc(params = @[bindSym"Value",
          newIdentDefs(runtimeArgs[i], bindSym"Value", newEmptyNode())],
          body = partialBody)
        adapterValue = newCall(bindSym"vHostFunc", partialProc)
    return newCall(bindSym"bindHostValue", bindingsSym, globalsSym,
                   nameLit, adapterValue)
  if binding.eponymTypes.len == 0:
    return newCall(bindSym"bindHostIntUnary", bindingsSym, globalsSym,
                   nameLit, binding.implementation)
  var typeIndexes: seq[int] = @[]
  let isNatType = proc(typeIndex: int): bool =
    if typeIndex < 0 or typeIndex >= binding.eponymTypes.len: return false
    let typeName = binding.eponymTypes[typeIndex]
    isCheckedNatType(checkedGlobals, typeName)
  if binding.eponymTypes.len == 2 and isNatType(1):
    typeIndexes = @[0]
  elif binding.eponymTypes.len == 2:
    typeIndexes = @[0, 1]
  elif binding.eponymTypes.len == 3 and isNatType(0):
    typeIndexes = @[1, 2]
  else:
    for i in 0 ..< binding.eponymTypes.len:
      typeIndexes.add(i)
  var typeArgs: seq[NimNode] = @[]
  for typeIndex in typeIndexes:
    let eponymName = binding.eponymTypes[typeIndex]
    var nimType: NimNode = nil
    for mapping in mappings:
      if mapping.eponymName == eponymName:
        nimType = mapping.nimType
        break
    if nimType.isNil:
      error("bindPostulate for '" & binding.postulateName &
        "' needs runtimeType(" & eponymName & ", NimType)")
    typeArgs.add(nimType)
  let natOpaqueHomogeneous = binding.eponymTypes.len == 3 and
    isNatType(0) and typeArgs[0].repr == typeArgs[1].repr
  let adapter =
    if binding.eponymTypes.len == 1: bindSym"bindHostOpaqueUnary"
    elif binding.eponymTypes.len == 2 and isNatType(1):
      bindSym"bindHostOpaqueNatUnary"
    elif binding.eponymTypes.len == 2: bindSym"bindHostOpaqueMapUnary"
    elif binding.eponymTypes.len == 3 and isNatType(0):
      if natOpaqueHomogeneous: bindSym"bindHostNatOpaqueBinary"
      else: bindSym"bindHostNatOpaqueMapBinary"
    elif binding.eponymTypes.len == 3: bindSym"bindHostOpaqueBinary"
    elif binding.eponymTypes.len == 4: bindSym"bindHostOpaqueTernary"
    elif binding.eponymTypes.len == 5: bindSym"bindHostOpaqueQuaternary"
    elif binding.eponymTypes.len == 6: bindSym"bindHostOpaqueQuinary"
    else:
      error("unsupported bindPostulate codec combination for '" &
            binding.postulateName & "'")
  var genericAdapter = newNimNode(nnkBracketExpr)
  genericAdapter.add(adapter)
  let genericTypeArgs = if natOpaqueHomogeneous: typeArgs[0 .. 0] else: typeArgs
  for typeArg in genericTypeArgs:
    genericAdapter.add(typeArg)
  var call = newCall(genericAdapter, bindingsSym, globalsSym, nameLit)
  if binding.eponymTypes.len == 2 and isNatType(1):
    call.add(newLit(binding.eponymTypes[0]))
  elif binding.eponymTypes.len == 3 and isNatType(0):
    call.add(newLit(binding.eponymTypes[1]))
    call.add(newLit(binding.eponymTypes[2]))
  else:
    for eponymName in binding.eponymTypes:
      call.add(newLit(eponymName))
  call.add(binding.implementation)
  call

proc unsupportedRuntimeWrapper(decl: NimNode, defName: string,
                               mappings: seq[HostRuntimeType],
                               records: seq[HostRecord]): NimNode =
  let params = decl[3]
  var reason = "unsupported generic or higher-order signature"
  if decl[2].kind != nnkEmpty:
    reason = "generic Eponym procedures do not yet have runtime wrappers"
  elif params.len == 0 or params[0].kind == nnkEmpty:
    reason = "Eponym procedure has no explicit runtime result type"
  elif runtimeNimType(params[0], mappings, records).isNil:
    reason = "no runtime codec for Eponym result type '" & repr(params[0]) & "'"
  else:
    for i in 1 ..< params.len:
      let p = params[i]
      if p.kind != nnkIdentDefs:
        reason = "unsupported Nim parameter declaration for Eponym procedure '" &
          defName & "'"
        break
      if runtimeNimType(p[^2], mappings, records).isNil:
        reason = "no runtime codec for Eponym parameter type '" & repr(p[^2]) & "'"
        break
  let name = ident(defName)
  let message = newLit("eponymBlock wrapper '" & defName & "': " & reason &
    "; add runtimeType for an opaque postulated type or use a supported primitive")
  result = quote do:
    template `name`*(args: varargs[untyped]): untyped =
      {.error: `message`.}

proc typedRuntimeWrapper(decl: NimNode, baseDir, src, defName: string,
                         bindings: seq[HostPostulateBinding],
                         mappings: seq[HostRuntimeType],
                         checkedGlobals: Globals,
                         records: seq[HostRecord]): NimNode =
  ## Emit concrete Nim wrappers for first-order types, including generic type
  ## variables represented as opaque host boxes.
  if decl.kind != nnkProcDef:
    return nil
  let generic = genericRuntimeInfo(decl, mappings)
  if generic.error.len > 0: return nil
  let codecMappings = generic.codecMappings
  let params = decl[3]
  if params.len == 0 or params[0].kind == nnkEmpty:
    return nil
  let resultType = runtimeNimType(params[0], codecMappings, records)
  if resultType.isNil: return nil

  var formal = newNimNode(nnkFormalParams)
  formal.add(ident("int"))
  var argSyms: seq[NimNode] = @[]
  var argEponymTypes: seq[NimNode] = @[]
  var argNimTypes: seq[NimNode] = @[]
  for i in 1 ..< params.len:
    let p = params[i]
    if p.kind != nnkIdentDefs: return nil
    let argType = runtimeNimType(p[^2], codecMappings, records)
    if argType.isNil: return nil
    for j in 0 ..< p.len - 2:
      let argName = if p[j].kind == nnkPragmaExpr: p[j][0] else: p[j]
      let argSym = genSym(nskParam, $argName)
      formal.add(newIdentDefs(argSym, argType, newEmptyNode()))
      argSyms.add(argSym)
      argEponymTypes.add(p[^2])
      argNimTypes.add(argType)

  formal[0] = resultType

  let dirLit = newLit(baseDir)
  let srcLit = newLit(src)
  let nameLit = newLit(defName)
  var wrapperBody = newStmtList()
  let globalsSym = genSym(nskLet, "checkedGlobals")
  wrapperBody.add(newLetStmt(globalsSym,
    newCall(bindSym"getGlobalsDir", dirLit, srcLit)))
  var bindingSym: NimNode = nil
  if bindings.len > 0:
    bindingSym = genSym(nskVar, "runtimeBindings")
    wrapperBody.add(newVarStmt(bindingSym,
      newCall(bindSym"initRuntimeBindings")))
    for binding in bindings:
      wrapperBody.add(bindingCall(binding, bindingSym, globalsSym,
                                  codecMappings, records, checkedGlobals))

  var values = newNimNode(nnkBracket)
  for _ in generic.typeNames:
    values.add(newCall(bindSym"vType", newLit(0)))
  for i, argSym in argSyms:
    values.add(runtimeValueConversionExpr(argEponymTypes[i], argNimTypes[i],
      argSym, true, codecMappings, records, globalsSym))
    if values[^1].isNil: return nil
  let valuesSeq = newTree(nnkPrefix, ident("@"), values)
  var callArgs = @[dirLit, srcLit, nameLit, valuesSeq]
  if not bindingSym.isNil: callArgs.add(bindingSym)
  let runtimeValue = genSym(nskLet, "runtimeValue")
  wrapperBody.add(newLetStmt(runtimeValue,
    newCall(bindSym"callValueFuncDir", callArgs)))
  let resultExpr = runtimeValueConversionExpr(params[0], resultType,
    runtimeValue, false, codecMappings, records, globalsSym)
  if resultExpr.isNil: return nil
  wrapperBody.add(resultExpr)

  result = newNimNode(nnkProcDef)
  result.add(newTree(nnkPostfix, ident("*"), ident(defName)))
  result.add(newEmptyNode())
  result.add(generic.genericParams)
  result.add(formal)
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(wrapperBody)

proc typedRuntimeValueWrapper(decl: NimNode, baseDir, src, defName: string,
                              bindings: seq[HostPostulateBinding],
                              mappings: seq[HostRuntimeType],
                              checkedGlobals: Globals,
                              records: seq[HostRecord]): NimNode =
  ## Emit a typed host-argument overload that returns the checked result as a
  ## Value. This keeps the definition's full Eponym signature while exposing
  ## only codecs explicitly described by runtimeType and the primitive codecs.
  if decl.kind != nnkProcDef:
    return nil
  let generic = genericRuntimeInfo(decl, mappings)
  if generic.error.len > 0: return nil
  let codecMappings = generic.codecMappings
  let params = decl[3]
  if params.len <= 1 or params[0].kind == nnkEmpty:
    return nil

  var formal = newNimNode(nnkFormalParams)
  formal.add(parseExpr("tuple[value: Value, globals: Globals]"))
  var argSyms: seq[NimNode] = @[]
  var eponymTypes: seq[NimNode] = @[]
  var nimTypes: seq[NimNode] = @[]
  for i in 1 ..< params.len:
    let p = params[i]
    if p.kind != nnkIdentDefs: return nil
    let nimType = runtimeNimType(p[^2], codecMappings, records)
    if nimType.isNil: return nil
    for j in 0 ..< p.len - 2:
      let argName = if p[j].kind == nnkPragmaExpr: p[j][0] else: p[j]
      let argSym = genSym(nskParam, $argName)
      formal.add(newIdentDefs(argSym, nimType, newEmptyNode()))
      argSyms.add(argSym)
      eponymTypes.add(p[^2])
      nimTypes.add(nimType)

  let globalsSym = genSym(nskLet, "runtimeGlobals")
  var values = newNimNode(nnkBracket)
  for _ in generic.typeNames:
    values.add(newCall(bindSym"vType", newLit(0)))
  for i, argSym in argSyms:
    let converted = runtimeValueConversionExpr(eponymTypes[i], nimTypes[i],
      argSym, true, codecMappings, records, globalsSym)
    if converted.isNil: return nil
    values.add(converted)
  let valuesSeq = newTree(nnkPrefix, ident("@"), values)
  let dirLit = newLit(baseDir)
  let srcLit = newLit(src)
  let nameLit = newLit(defName)
  let defsSym = genSym(nskLet, "runtimeDefs")
  let runtimeValueSym = genSym(nskLet, "runtimeValue")
  var body = newStmtList()
  body.add(newLetStmt(globalsSym,
    newCall(bindSym"getGlobalsDir", dirLit, srcLit)))
  body.add(newLetStmt(defsSym,
    newCall(bindSym"getDefsDir", dirLit, srcLit)))
  var bindingSym: NimNode = nil
  bindingSym = genSym(nskVar, "runtimeBindings")
  body.add(newVarStmt(bindingSym, newCall(bindSym"initRuntimeBindings")))
  if bindings.len > 0:
    for binding in bindings:
      body.add(bindingCall(binding, bindingSym, globalsSym, codecMappings,
                           records, checkedGlobals))
  let runtimeCall = newCall(bindSym"callDefValueWithBindings",
    newCall(bindSym"findDef", defsSym, nameLit), valuesSeq, bindingSym)
  body.add(newLetStmt(runtimeValueSym,
    runtimeCall))
  body.add(newTree(nnkTupleConstr, runtimeValueSym, globalsSym))

  result = newNimNode(nnkProcDef)
  result.add(newTree(nnkPostfix, ident("*"), ident(defName & "RuntimeValue")))
  result.add(newEmptyNode())
  result.add(generic.genericParams)
  result.add(formal)
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(body)

macro eponymBlock*(body: untyped): untyped =
  ## Elaborate a block of Nim-syntax Eponym definitions (no """).
  ## Uses call syntax: proc f(x: Int): Int = ..., postulate(I, Univ),
  ## data(N, Univ): block.
  ## Quantity binders (Issue #28/#64): `ch {.linear.}` / `ch {.erased.}`
  ## in proc/data params emit `(1 ch : ...)` / `(0 ch : ...)` binders.
  ## Dependent Pi/Sigma types: Pi(x: A, y {.linear.}: B, C),
  ## Sig(x: A, B), Sig(A, B).
  ## `import "path.ep"` (Issue #131): Eponym-module import, resolved
  ## relative to the Nim file containing the eponymBlock call; makes prelude
  ## definitions (lib/*.ep) available without redefinition.
  ## `elim(name, Ty)` / `red(lhs, rhs)` (Issue #151): eliminator and
  ## computation-rule declarations, e.g. the Bool/Nat eliminators of smoke
  ## tests 07/08.
  ## `def(name, Ty):` with a block of `clause([pat, ...], rhs)` (Issue #151):
  ## clause-style definitions; constructor-application patterns are
  ## parenthesized automatically.
  ## `byTac(name)` (Issue #151): tactic term (`by refl`, smoke test 14).
  ## `x {.qvar(q).}` (Issue #151): quantity-variable binder `(q x : T)`.
  ## Nim-safe name mappings: `vecnil` -> `nil`, `unitv` -> `<>`,
  ## `unitTy` -> `1` (unit type), `emptyTy` -> `O` (empty type).
  ## Generates callable fixed-arity wrappers for primitive Int/Nat and
  ## explicitly mapped opaque postulated types. Unsupported legacy shapes
  ## retain the varargs[int] compatibility wrapper.
  let src = blockToEponym(body)
  var runtimeValueNames = initHashSet[string]()
  for st in body:
    if st.kind == nnkCall and st.len == 2 and st[0].kind == nnkIdent and
        $st[0] == "runtimeValue":
      let name = $st[1]
      if name in runtimeValueNames:
        error("duplicate runtimeValue request for '" & name & "'", st)
      runtimeValueNames.incl(name)
  # Issue #131: imports resolve relative to the calling Nim file's dir.
  let baseDir = callerDir(body)
  var defs: seq[ElabDef]
  var checkedGlobals: Globals
  try:
    let checked = elabCheckDirState(src, baseDir)
    defs = checked.defs
    checkedGlobals = checked.globals
  except ElabError as e:
    error("eponymBlock elaboration error: " & e.msg, body)
  except ParseError as e:
    error("eponymBlock parse error: " & e.msg, body)

  for requested in runtimeValueNames:
    var found = false
    for d in defs:
      if d.name == requested: found = true
    if not found:
      error("runtimeValue names no checked definition: " & requested, body)
    var declaration: NimNode = nil
    for st in body:
      if st.kind == nnkProcDef and $st[0] == requested:
        declaration = st
        break
    if declaration.isNil or
        declaration[3].len == 0 or declaration[3][0].kind == nnkEmpty:
      error("runtimeValue requires a checked definition with a result: " &
        requested, body)
    if declaration[2].kind != nnkEmpty:
      let generic = genericRuntimeInfo(declaration, hostRuntimeTypes(body))
      if generic.error.len > 0:
        error("runtimeValue cannot expose '" & requested & "': " &
          generic.error, declaration)
    for i in 1 ..< declaration[3].len:
      if declaration[3][i].kind != nnkIdentDefs:
        error("runtimeValue supports ordinary fixed-arity parameters: " & requested,
          declaration)

  let bindings = hostPostulateBindings(body)
  for binding in bindings:
    if not bindingIsReferenced(body, binding.postulateName):
      error("eponymBlock binding error: binding for postulate '" &
        binding.postulateName & "' is unused by every proc body", body)
  let runtimeTypes = hostRuntimeTypes(body)
  let records = hostRecords(body)
  var usesBoolCodec = false
  for st in body:
    if st.kind == nnkProcDef and mentionsName(st[3], "Bool"):
      usesBoolCodec = true
  if usesBoolCodec:
    try:
      validateHostBoolCodec(checkedGlobals)
    except ValueError as e:
      error("eponymBlock runtimeType error: " & e.msg, body)
  for mapping in runtimeTypes:
    try:
      if findHostRecord(records, mapping.eponymName) < 0:
        validateHostOpaqueType(checkedGlobals, mapping.eponymName)
    except ValueError as e:
      error("eponymBlock runtimeType error: " & e.msg, body)
  for binding in bindings:
    try:
      if binding.rawValue:
        discard validateHostValueNaryType(checkedGlobals,
                                          binding.postulateName)
        continue
      if binding.pairResult:
        let pairArgs = binding.eponymTypes[0 ..< binding.pairArgCount]
        validateHostSigmaAdapterType(checkedGlobals,
          binding.postulateName, pairArgs,
          binding.eponymTypes[binding.pairArgCount],
          binding.eponymTypes[binding.pairArgCount + 1],
          binding.trustedPairIndex)
        continue
      case binding.eponymTypes.len
      of 0:
        validateHostIntUnaryType(checkedGlobals, binding.postulateName)
      of 1:
        let required = validateHostOpaqueUnaryType(checkedGlobals,
                                                    binding.postulateName)
        if required != binding.eponymTypes[0]:
          raise newException(ValueError,
            "postulate '" & binding.postulateName & "' requires opaque Eponym type '" &
            required & "', not '" & binding.eponymTypes[0] & "'")
      of 2:
        if isCheckedNatType(checkedGlobals, binding.eponymTypes[1]):
          validateHostOpaqueNatUnaryType(checkedGlobals,
            binding.postulateName, binding.eponymTypes[0])
        else:
          validateHostOpaqueMapUnaryType(checkedGlobals,
            binding.postulateName, binding.eponymTypes[0],
            binding.eponymTypes[1])
      of 3:
        if isCheckedNatType(checkedGlobals, binding.eponymTypes[0]):
          validateHostNatOpaqueBinaryType(checkedGlobals,
            binding.postulateName, binding.eponymTypes[1],
            binding.eponymTypes[2])
        else:
          validateHostOpaqueBinaryType(checkedGlobals, binding.postulateName,
            binding.eponymTypes[0], binding.eponymTypes[1],
            binding.eponymTypes[2])
      of 4:
        validateHostOpaqueTernaryType(checkedGlobals, binding.postulateName,
          binding.eponymTypes[0], binding.eponymTypes[1],
          binding.eponymTypes[2], binding.eponymTypes[3])
      of 5:
        validateHostOpaqueQuaternaryType(checkedGlobals,
          binding.postulateName, binding.eponymTypes[0],
          binding.eponymTypes[1], binding.eponymTypes[2],
          binding.eponymTypes[3], binding.eponymTypes[4])
      of 6:
        validateHostOpaqueQuinaryType(checkedGlobals,
          binding.postulateName, binding.eponymTypes[0],
          binding.eponymTypes[1], binding.eponymTypes[2],
          binding.eponymTypes[3], binding.eponymTypes[4],
          binding.eponymTypes[5])
      else:
        raise newException(ValueError,
          "bindPostulate supports Int -> Int, opaque T -> T, opaque T -> U, " &
          "opaque T -> Nat, Nat -> opaque T -> opaque U, opaque A -> B -> C, " &
          "opaque A -> B -> C -> D, opaque A -> B -> C -> D -> E, and " &
          "opaque A -> B -> C -> D -> E -> F")
    except ValueError as e:
      error("eponymBlock binding error: " & e.msg, body)

  result = newStmtList()
  let dirLit = newLit(baseDir)
  for d in defs:
    let procName = ident(d.name)
    let srcLit = newLit(src)
    let nameLit = newLit(d.name)
    var procDecl: NimNode = nil
    for st in body:
      if st.kind == nnkProcDef and $st[0] == d.name:
        procDecl = st
        break
    if not procDecl.isNil:
      if d.name in runtimeValueNames:
        let params = procDecl[3]
        let generic = genericRuntimeInfo(procDecl, runtimeTypes)
        var valueArity = 0
        for i in 1 ..< params.len:
          valueArity += params[i].len - 2
        let runtimeName = ident(d.name & "RuntimeValue")
        let globalsSym = genSym(nskLet, "runtimeGlobals")
        let defsSym = genSym(nskLet, "runtimeDefs")
        let bindingsSym = genSym(nskVar, "runtimeBindings")
        let argsSym = genSym(nskParam, "runtimeArguments")
        let runtimeArgsSym = newCall(bindSym"prependErasedTypeArgs",
          newLit(generic.typeNames.len), argsSym)
        let expectedArity = newLit(valueArity)
        var bindingStatements = newStmtList()
        for binding in bindings:
          bindingStatements.add(bindingCall(binding, bindingsSym, globalsSym,
                                            runtimeTypes, records,
                                            checkedGlobals))
        var rawBody = newStmtList()
        rawBody.add quote do:
          if `argsSym`.len != `expectedArity`:
            raise newException(ValueError,
              "runtimeValue argument count mismatch for " & `nameLit`)
        rawBody.add quote do:
            let `globalsSym` = getGlobalsDir(`dirLit`, `srcLit`)
            let `defsSym` = getDefsDir(`dirLit`, `srcLit`)
            var `bindingsSym` = initRuntimeBindings()
        rawBody.add(bindingStatements)
        rawBody.add quote do:
            (callDefValueWithBindings(findDef(`defsSym`, `nameLit`), `runtimeArgsSym`,
                                      `bindingsSym`), `globalsSym`)
        var rawProc = newNimNode(nnkProcDef)
        rawProc.add(newTree(nnkPostfix, ident("*"), runtimeName))
        rawProc.add(newEmptyNode())
        rawProc.add(newEmptyNode())
        var rawFormal = newNimNode(nnkFormalParams)
        rawFormal.add(parseExpr("tuple[value: Value, globals: Globals]"))
        rawFormal.add(newIdentDefs(argsSym,
          newTree(nnkBracketExpr, ident"openArray", bindSym"Value"),
          newEmptyNode()))
        rawProc.add(rawFormal)
        rawProc.add(newEmptyNode())
        rawProc.add(newEmptyNode())
        rawProc.add(rawBody)
        result.add(rawProc)
        if valueArity == 0:
          result.add quote do:
            proc `runtimeName`*(): tuple[value: Value, globals: Globals] =
              `runtimeName`([])
        else:
          let typedValueWrapper = typedRuntimeValueWrapper(procDecl,
            baseDir, src, d.name, bindings, runtimeTypes, checkedGlobals,
            records)
          if not typedValueWrapper.isNil:
            result.add(typedValueWrapper)
      let typedWrapper = typedRuntimeWrapper(procDecl, baseDir, src, d.name,
                                             bindings, runtimeTypes,
                                             checkedGlobals, records)
      if not typedWrapper.isNil:
        result.add(typedWrapper)
      else:
        result.add(unsupportedRuntimeWrapper(procDecl, d.name, runtimeTypes,
                                             records))
      continue
    if bindings.len == 0:
      result.add(quote do:
        proc `procName`*(args: varargs[int]): int =
          callIntFuncDir(`dirLit`, `srcLit`, `nameLit`, @args)
      )
    else:
      var wrapper = quote do:
        proc `procName`*(args: varargs[int]): int = discard
      let argsIdent = wrapper[3][1][0]
      let globalsId = genSym(nskLet, "checkedGlobals")
      let runtimeBindingsId = genSym(nskVar, "runtimeBindings")
      var wrapperBody = newStmtList()
      wrapperBody.add(quote do:
        let `globalsId` = getGlobalsDir(`dirLit`, `srcLit`)
        var `runtimeBindingsId` = initRuntimeBindings()
      )
      for binding in bindings:
        wrapperBody.add(bindingCall(binding, runtimeBindingsId, globalsId,
                                    runtimeTypes, records, checkedGlobals))
      wrapperBody.add(quote do:
        callIntFuncDir(`dirLit`, `srcLit`, `nameLit`, @`argsIdent`,
                       `runtimeBindingsId`)
      )
      wrapper[6] = wrapperBody
      result.add(wrapper)

macro eponym*(src: string): untyped =
  ## Elaborate and typecheck a surface program at compile time.
  ## On success expands to nothing; on failure compilation stops with an
  ## error pointing at the eponym"..." literal.
  let s = src.strVal  # src is a string literal (enforced by the signature)
  try:
    discard elabCheck(s)
  except ElabError as e:
    error("eponym elaboration error: " & e.msg, src)
  except ParseError as e:
    error("eponym parse error: " & e.msg, src)
  result = newStmtList()

when isMainModule:
  eponym"""
proc twice (A : Type 0) (f : A -> A) (x : A) : A =
  f (f x)
proc pairSwap (A : Type 0) (B : Type 0) (p : Sig (u : A). B) : Sig (v : B). A =
  (snd p, fst p)
"""
  echo "ok: eponym macro accepts well-typed programs at compile time"
