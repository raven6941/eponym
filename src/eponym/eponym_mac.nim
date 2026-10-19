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
import preterm
import qtt_dps
import parse_surf
import os  # issue #131: parentDir of the eponymBlock call site
import strutils
import sequtils
import sets
import std/options

template rawValue* {.pragma.}

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
  var fallback = nimExprToEponym(elseBranch)
  for i in countdown(branches.high, 0):
    let (condition, body) = branches[i]
    fallback = "ifThenElse (" & nimExprToEponym(condition) & ") (" &
      nimExprToEponym(branchExpr(body)) & ") (" & fallback & ")"
  fallback

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
    # the parser's unambiguous integer spelling `01`. The elaborator still
    # overloads it against the expected Nat or Int type.
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
      if arg.kind in {nnkCall, nnkCommand, nnkObjConstr, nnkBracketExpr,
                      nnkInfix, nnkPrefix}:
        parts.add("(" & value & ")")
      else:
        parts.add(value)
    parts.join(" ")
  of nnkInfix:
    case $n[0]
    of "+", "-", "*":
      let prim = case $n[0]
        of "+": "addInt"
        of "-": "subInt"
        else: "mulInt"
      prim & " (" & nimExprToEponym(n[1]) & ") (" &
        nimExprToEponym(n[2]) & ")"
    of "and", "or":
      # Nim's Boolean operators short-circuit. Eponym application evaluates
      # arguments eagerly, so delay the right side in a unit thunk and force
      # only the selected branch after the checked Bool eliminator chooses it.
      let left = nimExprToEponym(n[1])
      let right = nimExprToEponym(n[2])
      let yesBranch = if $n[0] == "and":
        "(lam (_ : 1). " & right & ")"
      else:
        "(lam (_ : 1). true)"
      let noBranch = if $n[0] == "and":
        "(lam (_ : 1). false)"
      else:
        "(lam (_ : 1). " & right & ")"
      "ifThenElse (" & left & ") " & yesBranch & " " & noBranch & " <>"
    of "xor":
      # Nim evaluates both operands of xor. Bind them before selecting so a
      # postulate on the right is evaluated exactly once in either branch.
      let leftName = $genSym(nskLet, "eponymXorLeft")
      let rightName = $genSym(nskLet, "eponymXorRight")
      "let " & leftName & " = " & nimExprToEponym(n[1]) & " in " &
        "let " & rightName & " = " & nimExprToEponym(n[2]) & " in " &
        "ifThenElse " & leftName & " (not " & rightName & ") " & rightName
    else:
      error("eponymBlock: unsupported pure operator '" & $n[0] & "'",
            n[0])
  of nnkPrefix:
    if $n[0] == "-":
      "subInt 0 (" & nimExprToEponym(n[1]) & ")"
    elif $n[0] == "not":
      "not (" & nimExprToEponym(n[1]) & ")"
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
  of nnkEmpty:
    "1" # Nim's omitted proc result type is Eponym unit.
  of nnkIdent:
    var s = $n
    # Map Nim-safe names to Eponym names (issue #144: same mapping as
    # expressions -- `nil` is a Nim keyword, so constructor references in
    # types must go through `vecnil` too)
    if s == "vecnil": s = "nil"
    if s == "unitv": s = "<>"   # issue #151: `<>` is not valid Nim syntax
    if s == "unitTy": s = "1"   # issue #151: the unit *type* (QTT)
    if s == "void": s = "1"
    if s == "emptyTy": s = "O"  # issue #151: the empty type
    if s == "Univ": "Type 0" else: s
  of nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit, nnkInt64Lit:
    # Integer literal in type position: passed through verbatim; the
    # elaborator overloads it against the expected type (Nat or Int),
    # exactly as in string syntax (Issues #8, #115).
    # Exception: 1 lexes as the *unit type* in surface syntax (QTT), so use
    # the parser's unambiguous integer spelling `01`; expected-type
    # overloading still selects Nat or Int.
    let v = n.intVal
    if v < 0: error("negative integer literal in type", n)
    if v == 1: "01" else: $v
  of nnkBracketExpr:
    if n.len < 2:
      error("eponymBlock: bracket type application needs explicit arguments", n)
    let head = nimTypeToEponym(n[0])
    var args: seq[string] = @[]
    for i in 1 ..< n.len:
      let a = n[i]
      if (a.kind == nnkCall and a.len > 1) or a.kind in
          {nnkObjConstr, nnkBracketExpr} or
          a.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                     nnkInt64Lit}:
        args.add("(" & nimTypeToEponym(a) & ")")
      else:
        args.add(nimTypeToEponym(a))
    head & " " & args.join(" ")
  of nnkProcTy:
    if n.len != 2 or n[0].kind != nnkFormalParams or n[0].len < 1:
      error("runtime proc types require ordinary arguments", n)
    var resultType = nimTypeToEponym(n[0][0])
    var params: seq[(string, NimNode)] = @[]
    for i in 1 ..< n[0].len:
      let p = n[0][i]
      if p.kind != nnkIdentDefs or p.len < 3:
        error("runtime proc types require ordinary named arguments", p)
      for j in 0 ..< p.len - 2:
        let name = if p[j].kind == nnkEmpty: "callbackArg" & $params.len
                   else: $p[j]
        params.add((name, p[^2]))
    if params.len == 0:
      return "Pi (_ : 1). " & resultType
    for i in countdown(params.high, 0):
      resultType = "Pi (" & params[i][0] & " : " &
        nimTypeToEponym(params[i][1]) & "). " & resultType
    resultType
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
        if st.len < 3 or st[1].kind != nnkIdent:
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
      elif head == "runtimeCodec":
        # Typed host codec for any named Eponym type or family.
        if st.len != 5 or st[1].kind != nnkIdent or
            st[3].kind notin {nnkIdent, nnkSym} or
            st[4].kind notin {nnkIdent, nnkSym}:
          error("runtimeCodec expects (EponymType, NimType, encoder, decoder)",
            st)
      elif head == "runtimeVector":
        # Structural runtime codec for a Vec family with canonical nil/cons
        # constructor names.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeVector expects (VecFamily)", st)
      elif head == "runtimeVectorArray":
        # Fixed-size array representation of the canonical Vec family.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeVectorArray expects (VecFamily)", st)
      elif head == "runtimeList":
        # Structural runtime codec for a List family with canonical nil/cons.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeList expects (ListFamily)", st)
      elif head == "runtimeOption":
        # Structural runtime codec for a unary Option family.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeOption expects (OptionFamily)", st)
      elif head == "runtimeVariant":
        # Raw structural codec for payload-bearing data families.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeVariant expects (DataFamily)", st)
      elif head == "runtimeDataVariant":
        # Recursive tagged representation for supported constructor fields.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeDataVariant expects (DataFamily)", st)
      elif head == "runtimeValue":
        # Request a raw Eponym Value wrapper for a checked definition,
        # typically for a host interpreter of reified data.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeValue expects (checkedDefinition)", st)
      elif head == "runtimeDps":
        # Request direct destination-passing code for a checked definition.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeDps expects (checkedDefinition)", st)
      elif head == "runtimePairTrusted":
        # Explicitly trust the host correspondence for dependent Sigma indices
        # in one generated definition's typed runtime interface.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimePairTrusted expects (checkedDefinition)", st)
      elif head == "runtimeRecordTrusted":
        # Explicitly trust host values to satisfy dependent record indices;
        # codecs still enforce any structural constraints they represent.
        if st.len != 2 or st[1].kind != nnkIdent:
          error("runtimeRecordTrusted expects (RecordType)", st)
      else:
        error("eponymBlock: unsupported call: " & head, st)
    else:
      error("eponymBlock: unsupported statement: " & $st.kind, st)

type HostPostulateBinding = object
  postulateName: string
  implementation: NimNode
  eponymTypes: seq[string]
  eponymTypeExprs: seq[NimNode]
  eponymArgumentNames: seq[string]
  pairResultType: NimNode
  pairResultArgNames: seq[string]
  pairResult: bool
  pairArgCount: int
  trustedPairIndex: bool
  rawValue: bool

type HostRuntimeType = object
  eponymName: string
  nimType: NimNode
  isSynthetic: bool
  isRuntimeVector: bool
  isRuntimeVectorArray: bool
  isRuntimeList: bool
  isRuntimeOption: bool
  isRuntimeVariant: bool
  isRuntimeStructuredVariant: bool
  isRuntimeCodec: bool
  isRuntimeIndexedType: bool
  isOpaqueRuntimeType: bool
  isGenericTypeBody: bool
  encoder: NimNode
  decoder: NimNode

proc mentionsName(node: NimNode, name: string): bool

type HostRecordField = object
  name: string
  eponymType: NimNode

type HostRecord = object
  name: string
  fields: seq[HostRecordField]
  hasDependentField: bool
  isVariant: bool
  constructors: seq[string]
  trustDependentFields: bool

proc hostRecords(body: NimNode,
                 trustedDependent: HashSet[string]): seq[HostRecord] =
  for st in body:
    if st.kind != nnkCall or st.len == 0 or st[0].kind != nnkIdent:
      continue
    let isRecord = $st[0] == "record" and st.len == 3 and
      st[2].kind == nnkStmtList
    let isVariant = $st[0] == "data" and st.len == 4 and
      st[3].kind == nnkStmtList
    if (not isRecord and not isVariant) or st[1].kind != nnkIdent:
      continue
    var record = HostRecord(name: $st[1], isVariant: isVariant,
      trustDependentFields: $st[1] in trustedDependent)
    if isVariant:
      for ctor in st[3]:
        if ctor.kind != nnkProcDef or ctor[0].kind != nnkIdent or
            ctor[3].kind != nnkFormalParams or ctor[3].len != 1 or
            ctor[3][0].kind != nnkIdent or $ctor[3][0] != record.name:
          record.hasDependentField = true
          break
        record.constructors.add($ctor[0])
      if record.constructors.len == 0:
        record.hasDependentField = true
      result.add(record)
      continue
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

proc hostRuntimeTypes(body: NimNode, globals: Globals): seq[HostRuntimeType] =
  var seen = initHashSet[string]()
  for st in body:
    if st.kind == nnkCall and st.len > 0 and st[0].kind == nnkIdent and
        $st[0] in ["runtimeType", "runtimeVector", "runtimeVectorArray", "runtimeList",
                   "runtimeOption", "runtimeVariant", "runtimeDataVariant",
                   "runtimeCodec"]:
      let isVector = $st[0] == "runtimeVector"
      let isVectorArray = $st[0] == "runtimeVectorArray"
      let isList = $st[0] == "runtimeList"
      let isOption = $st[0] == "runtimeOption"
      let isVariant = $st[0] == "runtimeVariant"
      let isStructuredVariant = $st[0] == "runtimeDataVariant"
      let isCodec = $st[0] == "runtimeCodec"
      if ((isVector or isVectorArray or isList or isOption or isVariant or
          isStructuredVariant) and
          (st.len != 2 or st[1].kind != nnkIdent)) or
          (isCodec and (st.len != 5 or st[1].kind != nnkIdent or
            st[3].kind notin {nnkIdent, nnkSym} or
            st[4].kind notin {nnkIdent, nnkSym})) or
          (not isVector and not isVectorArray and not isList and not isOption and not isVariant and
            not isStructuredVariant and not isCodec and
            (st.len != 3 or st[1].kind != nnkIdent)):
        error(if isVector: "runtimeVector expects (VecFamily)"
          elif isVectorArray: "runtimeVectorArray expects (VecFamily)"
          elif isList: "runtimeList expects (ListFamily)"
          elif isOption: "runtimeOption expects (OptionFamily)"
          elif isVariant: "runtimeVariant expects (DataFamily)"
          elif isStructuredVariant: "runtimeDataVariant expects (DataFamily)"
          elif isCodec: "runtimeCodec expects (EponymType, NimType, encoder, decoder)"
          else: "runtimeType expects (EponymType, NimType)", st)
      let name = $st[1]
      if name in seen:
        error("duplicate runtime type mapping for '" & name & "'", st)
      seen.incl(name)
      result.add(HostRuntimeType(eponymName: name,
        nimType: if isVector or isList: ident"seq"
          elif isVectorArray: ident"array"
          elif isVariant: bindSym"RuntimeVariant"
          elif isStructuredVariant: bindSym"RuntimeStructuredVariant"
          elif isOption: ident"Option" else: st[2],
        isRuntimeVector: isVector or isVectorArray,
        isRuntimeVectorArray: isVectorArray, isRuntimeList: isList,
        isRuntimeOption: isOption, isRuntimeVariant: isVariant,
        isRuntimeStructuredVariant: isStructuredVariant,
        isRuntimeCodec: isCodec,
        isRuntimeIndexedType: name in globals and
          not globals[name].ty.isNil and globals[name].ty.kind == tPi,
        isOpaqueRuntimeType: not isCodec and name in globals and
          not globals[name].tm.isNil and not globals[name].tm.refIsDefn,
        encoder: if isCodec: st[3] else: nil,
        decoder: if isCodec: st[4] else: nil))

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

proc runtimeTypeAfterArgs(n: NimNode, count: int,
    argNames: var seq[string]): NimNode =
  ## Extract the result type after the explicit arrows/Pi binders accepted by
  ## a typed pair adapter. Keep this original type AST so dependent Sigma
  ## codecs can see the actual index expressions from the postulate.
  if count < 0: return nil
  if count == 0: return copyNimTree(n)
  if n.kind == nnkInfix and n.len == 3 and $n[0] == "->":
    argNames.add("")
    return runtimeTypeAfterArgs(n[2], count - 1, argNames)
  if n.kind in {nnkCall, nnkObjConstr} and n.len >= 3 and
      n[0].kind == nnkIdent and $n[0] == "Pi":
    var remaining = count
    for i in 1 ..< n.len - 1:
      let binder = n[i]
      if binder.kind == nnkExprColonExpr:
        argNames.add(binderName(binder[0]))
        dec remaining
      elif binder.kind == nnkTableConstr:
        for _ in binder: argNames.add("")
        remaining -= binder.len
      else:
        return nil
      if remaining < 0: return nil
    return runtimeTypeAfterArgs(n[^1], remaining, argNames)
  nil

proc runtimeTermTypeAst(term: Term, ctx: seq[string],
    refNames: Table[int, string]): NimNode =
  if term.isNil: return nil
  case term.kind
  of tR:
    if term.refId in refNames: ident(refNames[term.refId]) else: nil
  of tV:
    if term.idx >= 0 and term.idx < ctx.len: ident(ctx[term.idx]) else: nil
  of tPi, tSi:
    let binderName = if term.scope.adv.len > 0 and term.scope.adv != "_":
      term.scope.adv else: "runtimeIndex" & $ctx.len
    let domain = runtimeTermTypeAst(term.dom, ctx, refNames)
    let body = runtimeTermTypeAst(term.scope.bdy,
      @[binderName] & ctx, refNames)
    if domain.isNil or body.isNil: return nil
    let binder = newTree(nnkExprColonExpr, ident(binderName), domain)
    newCall(if term.kind == tPi: ident"Pi" else: ident"Sig", binder, body)
  of tApp:
    var args: seq[Term] = @[]
    var head = term
    while not head.isNil and head.kind == tApp:
      args.add(head.arg)
      head = head.fn
    let callee = runtimeTermTypeAst(head, ctx, refNames)
    if callee.isNil: return nil
    var application = newCall(callee)
    for i in countdown(args.high, 0):
      let arg = runtimeTermTypeAst(args[i], ctx, refNames)
      if arg.isNil: return nil
      application.add(arg)
    application
  of tInt: newLit(term.intVal)
  of tNatLit: newLit(term.natLitVal)
  of tNatSing: newLit(term.natSingVal)
  of tType:
    if term.lvl == 0: ident"Univ" else: nil
  else: nil

proc runtimeTermNimTypeAst(term: Term, ctx: seq[string],
    refNames: Table[int, string]): NimNode =
  ## Rebuild runtime-capable Eponym types as Nim types. A Pi occurring in a
  ## value position is a Nim closure type; top-level Pis are flattened by
  ## importedRuntimeProcDecl into ordinary proc parameters.
  if term.isNil: return nil
  if term.kind != tPi:
    return runtimeTermTypeAst(term, ctx, refNames)
  var current = term
  var callbackCtx = ctx
  var formal = newNimNode(nnkFormalParams)
  var argumentIndex = 0
  var nullary = false
  while not current.isNil and current.kind == tPi:
    if current.dom.kind == tC and current.dom.c == cOne:
      if argumentIndex == 0:
        nullary = true
        current = current.scope.bdy
      break
    if current.impl or current.qty != qOmega or current.dom.isNil or
        current.dom.kind == tType:
      return nil
    let argumentName = if current.scope.adv.len > 0 and
        current.scope.adv != "_": current.scope.adv
      else: "callbackArg" & $argumentIndex
    let argumentType = runtimeTermNimTypeAst(current.dom, callbackCtx,
      refNames)
    if argumentType.isNil: return nil
    formal.add(newIdentDefs(ident(argumentName), argumentType,
      newEmptyNode()))
    callbackCtx = @[argumentName] & callbackCtx
    current = current.scope.bdy
    inc argumentIndex
  if argumentIndex == 0 and not nullary: return nil
  let resultType = runtimeTermNimTypeAst(current, callbackCtx, refNames)
  if resultType.isNil: return nil
  formal.insert(0, resultType)
  result = newTree(nnkProcTy, formal, newTree(nnkPragma, ident"closure"))

proc hasImportedNullaryUnitArgument(decl: NimNode): bool =
  if decl.kind != nnkProcDef or decl.len < 5 or
      decl[4].kind != nnkPragma:
    return false
  for pragma in decl[4]:
    if pragma.kind in {nnkIdent, nnkSym} and
        $pragma == "eponymRuntimeNullaryUnit":
      return true

proc runtimeTermTypeAfterArgs(ty: Term, count: int, globals: Globals):
    tuple[resultType: NimNode, argNames: seq[string]] =
  var current = ty
  for i in 0 ..< count:
    if current.isNil or current.kind != tPi: return
    let binderName = if current.scope.adv.len > 0 and
        current.scope.adv != "_": current.scope.adv
      else: "runtimePairArg" & $i
    result.argNames.add(if current.scope.adv == "_": "" else: binderName)
    current = current.scope.bdy
  var refNames = initTable[int, string]()
  for name, entry in globals:
    if not entry.tm.isNil and entry.tm.kind == tR:
      refNames[entry.tm.refId] = name
  var ctx = newSeq[string](result.argNames.len)
  for i, name in result.argNames:
    ctx[result.argNames.high - i] = if name.len == 0:
      "runtimePairArg" & $i else: name
  result.resultType = runtimeTermTypeAst(current, ctx, refNames)

proc importedRuntimeProcDecl(definition: ElabDef,
                             globals: Globals): NimNode =
  ## Rebuild a simple imported Pi signature as a synthetic Nim proc AST so
  ## the ordinary codec generator can emit typed wrappers for it.
  var refNames = initTable[int, string]()
  for name, entry in globals:
    if not entry.tm.isNil and entry.tm.kind == tR:
      refNames[entry.tm.refId] = name
  var current = definition.tyTm
  var ctx: seq[string] = @[]
  var genericParams = newNimNode(nnkGenericParams)
  var formal = newNimNode(nnkFormalParams)
  formal.add(newEmptyNode())
  var argumentIndex = 0
  var lambdaIndex = 0
  var nullaryUnitArgument = false
  var checkedBody = definition.tmTm
  var argumentCount = 0
  while not checkedBody.isNil and checkedBody.kind == tLam:
    inc argumentCount
    checkedBody = checkedBody.scope.bdy
  while lambdaIndex < argumentCount:
    if current.isNil or current.kind != tPi: return nil
    if current.dom.isNil:
      return nil
    let name = if current.scope.adv.len > 0 and
        current.scope.adv != "_": current.scope.adv
      else: "runtimeArg" & $lambdaIndex
    if current.dom.kind == tType and current.dom.lvl == 0:
      if current.qty notin {q0, qOmega}: return nil
      genericParams.add(newIdentDefs(ident(name), ident"Univ",
        newEmptyNode()))
      ctx = @[name] & ctx
      current = current.scope.bdy
      inc lambdaIndex
      continue
    if current.impl:
      if current.qty notin {q0, qOmega}: return nil
      let genericType = runtimeTermTypeAst(current.dom, ctx, refNames)
      if genericType.isNil: return nil
      genericParams.add(newIdentDefs(ident(name), genericType,
        newEmptyNode()))
      ctx = @[name] & ctx
      current = current.scope.bdy
      inc lambdaIndex
      continue
    if current.qty != qOmega:
      return nil
    if current.dom.kind == tC and current.dom.c == cOne:
      if argumentCount != 1 or lambdaIndex != 0 or argumentIndex != 0 or
          genericParams.len != 0:
        return nil
      nullaryUnitArgument = true
      current = current.scope.bdy
      ctx = @[name] & ctx
      inc lambdaIndex
      continue
    let argType = runtimeTermNimTypeAst(current.dom, ctx, refNames)
    if argType.isNil: return nil
    formal.add(newIdentDefs(ident(name), argType, newEmptyNode()))
    ctx = @[name] & ctx
    current = current.scope.bdy
    inc lambdaIndex
    inc argumentIndex
  if argumentIndex == 0 and genericParams.len == 0 and
      not nullaryUnitArgument: return nil
  let resultType = runtimeTermNimTypeAst(current, ctx, refNames)
  if resultType.isNil: return nil
  formal[0] = resultType
  result = newNimNode(nnkProcDef)
  result.add(ident(definition.name))
  result.add(newEmptyNode())
  result.add(if genericParams.len > 0: genericParams else: newEmptyNode())
  result.add(formal)
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  if nullaryUnitArgument:
    result[4] = newTree(nnkPragma, ident"eponymRuntimeNullaryUnit")

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
          error("bindPostulatePair expects (name, nimProc, Argument[, Argument...], First, Second)", st)
      elif st.len < 3 or st[1].kind != nnkIdent:
        error("bindPostulate expects (postulateName, nimProcedure[, EponymType...])", st)
      let name = $st[1]
      if name in seen:
        error("duplicate bindPostulate for '" & name & "'", st)
      seen.incl(name)
      var typeNames: seq[string] = @[]
      var typeExprs: seq[NimNode] = @[]
      for i in 3 ..< st.len:
        typeExprs.add(copyNimTree(st[i]))
        typeNames.add(if st[i].kind == nnkIdent: $st[i]
          else: nimTypeToEponym(st[i]))
      var pairResultType: NimNode = nil
      var pairResultArgNames: seq[string] = @[]
      if pairResult:
        for declaration in body:
          if declaration.kind == nnkCall and declaration.len == 3 and
              declaration[0].kind == nnkIdent and
              $declaration[0] == "postulate" and
              declaration[1].kind == nnkIdent and
              $declaration[1] == name:
            pairResultType = runtimeTypeAfterArgs(declaration[2],
              typeNames.len - 2, pairResultArgNames)
            break
      result.add(HostPostulateBinding(postulateName: name,
                                     implementation: st[2],
                                     eponymTypes: typeNames,
                                     eponymTypeExprs: typeExprs,
                                     pairResultType: pairResultType,
                                     pairResultArgNames: pairResultArgNames,
                                     pairResult: pairResult,
                                     pairArgCount: if pairResult:
                                       typeNames.len - 2 else: 0,
                                     trustedPairIndex: trustedPairIndex,
                                     rawValue: rawValue))

proc localPostulateArrowTypes(body: NimNode,
                              postulateName: string): seq[NimNode] =
  for declaration in body:
    if declaration.kind == nnkCall and declaration.len == 3 and
        declaration[0].kind == nnkIdent and $declaration[0] == "postulate" and
        declaration[1].kind == nnkIdent and $declaration[1] == postulateName:
      result.add(declaration[2])
      return

proc validateLocalBindingTypeExpressions(body: NimNode,
                                         binding: HostPostulateBinding) =
  if binding.eponymTypeExprs.len == 0 or binding.pairResult or
      binding.rawValue: return
  let declared = localPostulateArrowTypes(body, binding.postulateName)
  if declared.len == 0: return # imported or explicitly Pi-encoded declaration
  if declared[0].kind in {nnkCall, nnkObjConstr} and declared[0].len > 0 and
      declared[0][0].kind == nnkIdent and $declared[0][0] == "Pi":
    return # the checked Pi telescope below supplies the exact comparison
  var provided = binding.eponymTypeExprs.mapIt(nimTypeToEponym(it))
  if binding.eponymTypeExprs.len == 1:
    provided = @[provided[0], provided[0]]
  let providedType = provided.join(" -> ")
  let declaredType = nimTypeToEponym(declared[0])
  if providedType != declaredType:
    raise newException(ValueError,
      "typed adapter type '" & providedType & "' does not match postulate '" &
      binding.postulateName & "' (" & declaredType & ")")

proc stripOuterTypeParens(value: string): string =
  if value.len >= 2 and value[0] == '(' and value[^1] == ')':
    value[1 ..< value.len - 1]
  else:
    value

proc checkedTypeMatches(term: Term, typeExpr: NimNode, ctx: Ctx,
                        refNames: Table[int, string]): bool =
  if typeExpr.kind != nnkProcTy:
    if typeExpr.kind in {nnkCall, nnkObjConstr} and typeExpr.len == 3 and
        typeExpr[0].kind == nnkIdent and $typeExpr[0] == "Sig":
      if term.isNil or term.kind != tSi: return false
      let binder = typeExpr[1]
      var domainType: NimNode
      var name = ""
      if binder.kind == nnkExprColonExpr and binder.len == 2:
        domainType = binder[1]
        name = binderName(binder[0])
      else:
        domainType = binder
      if not checkedTypeMatches(term.dom, domainType, ctx, refNames):
        return false
      let checkedName = if term.scope.adv == "_": name
                        else: term.scope.adv
      let nestedCtx = if checkedName.len == 0: ctx else:
        @[CtxEntry(name: checkedName, ty: term.dom, qty: qOmega)] & ctx
      return checkedTypeMatches(term.scope.bdy, typeExpr[2], nestedCtx,
        refNames)
    return stripOuterTypeParens(prettyTerm(term, ctx, refNames)) ==
      nimTypeToEponym(typeExpr)
  if typeExpr.len != 2 or typeExpr[0].kind != nnkFormalParams or
      typeExpr[0].len < 1:
    return false
  var current = term
  var callbackCtx = ctx
  var argIndex = 0
  for i in 1 ..< typeExpr[0].len:
    let param = typeExpr[0][i]
    if param.kind != nnkIdentDefs or param.len < 3:
      return false
    for j in 0 ..< param.len - 2:
      if current.isNil or current.kind != tPi or current.impl or
          current.qty == q0:
        return false
      let actual = stripOuterTypeParens(
        prettyTerm(current.dom, callbackCtx, refNames))
      let wanted = nimTypeToEponym(param[^2])
      if actual != wanted: return false
      let name = if param[j].kind == nnkEmpty: "callbackArg" & $argIndex
                 else: binderName(param[j])
      let checkedName = if current.scope.adv == "_": name
                        else: current.scope.adv
      callbackCtx = @[CtxEntry(name: checkedName, ty: current.dom,
        qty: current.qty)] & callbackCtx
      current = current.scope.bdy
      inc argIndex
  if argIndex == 0:
    if current.isNil or current.kind != tPi or current.impl or
        current.qty == q0 or current.dom.kind != tC or
        current.dom.c != cOne:
      return false
    current = current.scope.bdy
  stripOuterTypeParens(prettyTerm(current, callbackCtx, refNames)) ==
    nimTypeToEponym(typeExpr[0][0])

proc validateAppliedBindingTypeExpressions(globals: Globals,
    binding: HostPostulateBinding) =
  if binding.eponymTypeExprs.len == 0 or binding.pairResult or
      binding.rawValue: return
  var hasAppliedType = false
  for typeExpr in binding.eponymTypeExprs:
    if typeExpr.kind != nnkIdent: hasAppliedType = true
  if not hasAppliedType: return
  if binding.postulateName notin globals:
    raise newException(ValueError,
      "postulate not found: " & binding.postulateName)
  let entry = globals[binding.postulateName]
  var refNames = initTable[int, string]()
  for name, globalEntry in globals:
    if not globalEntry.tm.isNil and globalEntry.tm.kind == tR and
        globalEntry.tm.refId notin refNames:
      refNames[globalEntry.tm.refId] = name
  var expected = binding.eponymTypeExprs
  if expected.len == 1: expected = @[expected[0], expected[0]]
  var current = entry.ty
  var ctx: Ctx = @[]
  for i in 0 ..< expected.len - 1:
    if current.isNil or current.kind != tPi or current.impl or
        current.qty == q0:
      raise newException(ValueError,
        "typed adapter signature does not match postulate '" &
        binding.postulateName & "'")
    let wanted = nimTypeToEponym(expected[i])
    if not checkedTypeMatches(current.dom, expected[i], ctx, refNames):
      let actual = stripOuterTypeParens(prettyTerm(current.dom, ctx, refNames))
      raise newException(ValueError,
        "typed adapter type '" & wanted & "' does not match type " &
        $(i + 1) & " of postulate '" & binding.postulateName & "' (" &
        actual & ")")
    let binderName = if current.scope.adv == "_": "bindingArg" & $i
                     else: current.scope.adv
    ctx = @[CtxEntry(name: binderName, ty: current.dom, qty: current.qty)] & ctx
    current = current.scope.bdy
  let wantedResult = nimTypeToEponym(expected[^1])
  if not checkedTypeMatches(current, expected[^1], ctx, refNames):
    let actualResult = stripOuterTypeParens(prettyTerm(current, ctx, refNames))
    raise newException(ValueError,
      "typed adapter result type '" & wantedResult &
      "' does not match the result of postulate '" & binding.postulateName &
      "' (" & actualResult & ")")

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

proc termReferencesRef(term: Term, refId: int): bool =
  ## Whether a checked term mentions a global, including under binders.
  if term.isNil: return false
  case term.kind
  of tR: term.refId == refId
  of tPi, tSi, tLam:
    termReferencesRef(term.dom, refId) or
      termReferencesRef(term.scope.bdy, refId)
  of tPair:
    termReferencesRef(term.pFst, refId) or
      termReferencesRef(term.pSnd, refId) or
      termReferencesRef(term.pScope.bdy, refId)
  of tApp: termReferencesRef(term.fn, refId) or termReferencesRef(term.arg, refId)
  of tFst, tSnd, tAbsurd: termReferencesRef(term.sub, refId)
  of tLet:
    termReferencesRef(term.letVal, refId) or
      termReferencesRef(term.letTy, refId) or
      termReferencesRef(term.letScope.bdy, refId)
  of tMeta:
    for item in term.metaSpine:
      if termReferencesRef(item, refId): return true
    false
  of tV, tC, tType, tInt, tNatLit, tNatSing, tPrim: false

proc checkedDefReferences(definition: ElabDef, refId: int): bool =
  termReferencesRef(definition.tyTm, refId) or
    termReferencesRef(definition.tmTm, refId)

proc bindingIsReferenced(body: NimNode, postulateName: string,
                         allDefs: seq[ElabDef], globals: Globals): bool =
  ## Keep checking local Nim bodies, and include checked imported bodies.
  if bindingIsReferenced(body, postulateName): return true
  if postulateName notin globals: return false
  let refId = globals[postulateName].tm.refId
  for definition in allDefs:
    if checkedDefReferences(definition, refId): return true
  false

proc simpleRuntimeCodec(n: NimNode): string =
  if n.kind == nnkIdent:
    case $n
    of "Int": result = "int"
    of "Nat": result = "nat"
    of "Bool": result = "bool"
    else: result = ""

proc trustedRuntimePairNames(body: NimNode): HashSet[string] =
  result = initHashSet[string]()
  for st in body:
    if st.kind == nnkCall and st.len > 0 and st[0].kind == nnkIdent and
        $st[0] == "runtimePairTrusted":
      let name = $st[1]
      if name in result:
        error("duplicate runtimePairTrusted declaration for '" & name & "'", st)
      result.incl(name)

proc trustedRuntimeRecordNames(body: NimNode): HashSet[string] =
  result = initHashSet[string]()
  for st in body:
    if st.kind == nnkCall and st.len > 0 and st[0].kind == nnkIdent and
        $st[0] == "runtimeRecordTrusted":
      if st.len != 2 or st[1].kind != nnkIdent:
        error("runtimeRecordTrusted expects (RecordType)", st)
      let name = $st[1]
      if name in result:
        error("duplicate runtimeRecordTrusted declaration for '" & name & "'", st)
      result.incl(name)

proc runtimeSigmaComponents(n: NimNode, allowDependent = false):
    tuple[first, second: NimNode, binder: string] =
  ## Runtime tuples represent two-field Sig types. Unless the enclosing
  ## definition or record explicitly trusts dependent indices, reject a
  ## dependent tail rather than erase the first component from its type.
  if n.kind notin {nnkCall, nnkObjConstr} or n.len != 3 or
      n[0].kind != nnkIdent or
      $n[0] != "Sig":
    return
  if n[1].kind == nnkExprColonExpr:
    if n[1].len != 2 or n[1][0].kind != nnkIdent or
        (mentionsName(n[2], $n[1][0]) and not allowDependent):
      return
    return (n[1][1], n[2], $n[1][0])
  (n[1], n[2], "")

proc runtimeSigmaFields(n: NimNode, allowDependent = false):
    seq[tuple[fieldType: NimNode, binder: string]] =
  ## Flatten a right-nested Sigma telescope for Nim tuple codecs. The final
  ## field is the non-Sigma tail; each preceding binder scopes over later
  ## fields, matching Eponym's right-associated pair representation.
  var current = n
  while current.kind in {nnkCall, nnkObjConstr} and current.len == 3 and
      current[0].kind == nnkIdent and $current[0] == "Sig":
    let binder = current[1]
    if binder.kind == nnkExprColonExpr:
      if binder.len != 2 or binder[0].kind != nnkIdent or
          (mentionsName(current[2], $binder[0]) and not allowDependent):
        return @[]
      result.add((current[1][1], $binder[0]))
    else:
      result.add((current[1], ""))
    current = current[2]
  if result.len == 0: return
  result.add((current, ""))

proc runtimeVectorComponents(n: NimNode, familyName: string):
    tuple[elementType, length: NimNode] =
  if n.kind notin {nnkCall, nnkObjConstr, nnkBracketExpr} or n.len != 3 or
      n[0].kind != nnkIdent or $n[0] != familyName:
    return
  (n[1], n[2])

proc runtimeArrayLengthTypeExpr(n: NimNode): NimNode =
  ## Convert the supported Nat index grammar to a Nim compile-time array size.
  if n.isNil: return nil
  if n.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                nnkInt64Lit}:
    if n.intVal < 0: return nil
    return newLit(int(n.intVal))
  if n.kind in {nnkIdent, nnkSym}:
    if $n == "zero": return newLit(0)
    return copyNimTree(n)
  if n.kind == nnkPar and n.len == 1:
    return runtimeArrayLengthTypeExpr(n[0])
  if n.kind in {nnkCall, nnkCommand} and n.len >= 2 and
      n[0].kind in {nnkIdent, nnkSym}:
    let op = $n[0]
    if op == "suc" and n.len == 2:
      let value = runtimeArrayLengthTypeExpr(n[1])
      if value.isNil: return nil
      return newTree(nnkInfix, ident"+", value, newLit(1))
    if op in ["add", "mul"] and n.len == 3:
      let left = runtimeArrayLengthTypeExpr(n[1])
      let right = runtimeArrayLengthTypeExpr(n[2])
      if left.isNil or right.isNil: return nil
      return newTree(nnkInfix, ident(if op == "add": "+" else: "*"),
        left, right)
  if n.kind == nnkInfix and n.len == 3 and $n[0] in ["+", "*"]:
    let left = runtimeArrayLengthTypeExpr(n[1])
    let right = runtimeArrayLengthTypeExpr(n[2])
    if left.isNil or right.isNil: return nil
    return newTree(nnkInfix, copyNimTree(n[0]), left, right)
  nil

proc runtimeListElementType(n: NimNode, familyName: string): NimNode =
  if n.kind notin {nnkCall, nnkObjConstr, nnkBracketExpr} or n.len != 2 or
      n[0].kind != nnkIdent or $n[0] != familyName:
    return nil
  n[1]

proc runtimeOptionElementType(n: NimNode, familyName: string): NimNode =
  if n.kind notin {nnkCall, nnkObjConstr, nnkBracketExpr} or n.len != 2 or
      n[0].kind != nnkIdent or $n[0] != familyName:
    return nil
  n[1]

proc runtimeTypeHead(n: NimNode): NimNode =
  result = n
  while result.kind in {nnkCall, nnkCommand, nnkBracketExpr} and result.len > 0:
    result = result[0]

proc runtimeNatIndexExpr(n: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]] = @[]): NimNode =
  ## Lower supported Nat index expressions to checked Nim int arithmetic,
  ## substituting nearer Sigma/record binders as ordinary Nim operands.
  if n.kind in {nnkIdent, nnkSym}:
    if overrides.len > 0:
      for i in countdown(overrides.high, 0):
        if $n == overrides[i].name:
          return copyNimTree(overrides[i].value)
    if $n == "zero": return newLit(0)
    return copyNimTree(n)
  if n.kind == nnkDotExpr:
    return copyNimTree(n)
  if n.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                nnkInt64Lit}:
    if n.intVal < 0: return nil
    return copyNimTree(n)
  if n.kind == nnkCall and n.len >= 2 and n[0].kind == nnkIdent:
    case $n[0]
    of "suc":
      if n.len != 2: return nil
      let index = runtimeNatIndexExpr(n[1], overrides)
      if index.isNil: return nil
      return newCall(bindSym"natIndexSucc", index)
    of "add", "mul":
      if n.len != 3: return nil
      let left = runtimeNatIndexExpr(n[1], overrides)
      let right = runtimeNatIndexExpr(n[2], overrides)
      if left.isNil or right.isNil: return nil
      return newCall(if $n[0] == "add": bindSym"natIndexAdd" else:
        bindSym"natIndexMul", left, right)
  nil

type RuntimeProcParts = object
  argTypes: seq[NimNode]
  argNames: seq[string]
  resultType: NimNode
  isNullary: bool

proc runtimeProcParts(n: NimNode): RuntimeProcParts =
  if n.kind == nnkProcTy:
    if n.len != 2 or n[0].kind != nnkFormalParams or n[0].len < 1:
      return
    for i in 1 ..< n[0].len:
      let p = n[0][i]
      if p.kind != nnkIdentDefs or p.len < 3:
        return RuntimeProcParts()
      for j in 0 ..< p.len - 2:
        result.argTypes.add(p[^2])
        result.argNames.add(if p[j].kind == nnkEmpty: "callbackArg" &
          $result.argNames.len else: binderName(p[j]))
    result.resultType = n[0][0]
    result.isNullary = result.argTypes.len == 0
    return
  var current = n
  var foundFunctionType = false
  while true:
    if current.kind == nnkInfix and current.len == 3 and
        $current[0] == "->":
      foundFunctionType = true
      result.argTypes.add(current[1])
      result.argNames.add("callbackArg" & $result.argNames.len)
      current = current[2]
      continue
    if current.kind in {nnkCall, nnkObjConstr} and current.len >= 3 and
        current[0].kind in {nnkIdent, nnkSym} and $current[0] == "Pi":
      foundFunctionType = true
      for i in 1 ..< current.len - 1:
        let binder = current[i]
        if binder.kind != nnkExprColonExpr or binder.len != 2:
          return RuntimeProcParts()
        result.argTypes.add(binder[1])
        result.argNames.add(binderName(binder[0]))
      current = current[^1]
      continue
    break
  if not foundFunctionType: return RuntimeProcParts()
  result.resultType = current
  result.isNullary = result.argTypes.len == 0

proc hasClosurePragma(n: NimNode): bool =
  if n.kind == nnkProcTy and n.len == 2 and n[1].kind == nnkPragma:
    for pragma in n[1]:
      if pragma.kind in {nnkIdent, nnkSym} and $pragma == "closure":
        return true

proc hasRawValuePragma(n: NimNode): bool =
  if n.kind == nnkProcTy and n.len == 2 and n[1].kind == nnkPragma:
    for pragma in n[1]:
      if pragma.kind in {nnkIdent, nnkSym} and $pragma == "rawValue":
        return true

proc rawValueCallbackType(n: NimNode): NimNode =
  result = copyNimTree(n)
  result[0][0] = bindSym"Value"
  for i in 1 ..< result[0].len:
    result[0][i][^2] = bindSym"Value"

proc runtimeNimType(n: NimNode, mappings: seq[HostRuntimeType],
                    records: seq[HostRecord],
                    allowDependentSigma = false): NimNode =
  if n.kind == nnkEmpty or (n.kind == nnkIdent and $n in ["void", "unitTy"]):
    return newEmptyNode()
  let procParts = runtimeProcParts(n)
  if not procParts.resultType.isNil:
    if n.kind == nnkProcTy and not hasClosurePragma(n): return nil
    if n.kind == nnkProcTy and hasRawValuePragma(n):
      return rawValueCallbackType(n)
    let resultType = runtimeNimType(procParts.resultType, mappings, records,
                                    allowDependentSigma)
    if resultType.isNil: return nil
    if n.kind == nnkProcTy:
      result = copyNimTree(n)
      result[0][0] = resultType
      var argIndex = 0
      for i in 1 ..< result[0].len:
        let param = result[0][i]
        let argType = runtimeNimType(procParts.argTypes[argIndex], mappings,
          records, allowDependentSigma)
        if argType.isNil: return nil
        param[^2] = argType
        argIndex += param.len - 2
      return
    var formal = newTree(nnkFormalParams, resultType)
    for i, eponymArgType in procParts.argTypes:
      let argType = runtimeNimType(eponymArgType, mappings, records,
        allowDependentSigma)
      if argType.isNil: return nil
      formal.add(newIdentDefs(ident(procParts.argNames[i]), argType,
        newEmptyNode()))
    result = newTree(nnkProcTy, formal,
      newTree(nnkPragma, ident"closure"))
    return
  let typeHead = runtimeTypeHead(n)
  if typeHead.kind == nnkIdent:
    for mapping in mappings:
      if mapping.isRuntimeCodec and mapping.eponymName == $typeHead:
        return mapping.nimType
      if mapping.isRuntimeVariant and mapping.eponymName == $typeHead:
        return bindSym"RuntimeVariant"
      if mapping.isRuntimeStructuredVariant and
          mapping.eponymName == $typeHead:
        return bindSym"RuntimeStructuredVariant"
  for mapping in mappings:
    if mapping.isRuntimeVector:
      let vector = runtimeVectorComponents(n, mapping.eponymName)
      if not vector.elementType.isNil:
        if runtimeNatIndexExpr(vector.length).isNil: return nil
        let elementType = runtimeNimType(vector.elementType, mappings,
          records, allowDependentSigma)
        if elementType.isNil: return nil
        if mapping.isRuntimeVectorArray:
          let lengthType = runtimeArrayLengthTypeExpr(vector.length)
          if lengthType.isNil: return nil
          return newTree(nnkBracketExpr, ident"array", lengthType,
            elementType)
        return newTree(nnkBracketExpr, ident"seq", elementType)
    elif mapping.isRuntimeList:
      let listElement = runtimeListElementType(n, mapping.eponymName)
      if not listElement.isNil:
        let elementType = runtimeNimType(listElement, mappings, records,
          allowDependentSigma)
        if elementType.isNil: return nil
        return newTree(nnkBracketExpr, ident"seq", elementType)
    elif mapping.isRuntimeOption:
      let elementType = runtimeOptionElementType(n, mapping.eponymName)
      if not elementType.isNil:
        let nimElementType = runtimeNimType(elementType, mappings, records,
          allowDependentSigma)
        if nimElementType.isNil: return nil
        return newTree(nnkBracketExpr, bindSym"Option", nimElementType)
  let sigmaFields = runtimeSigmaFields(n, allowDependentSigma)
  if sigmaFields.len >= 2:
    result = newNimNode(nnkTupleConstr)
    for field in sigmaFields:
      let fieldType = runtimeNimType(field.fieldType, mappings, records,
        allowDependentSigma)
      if fieldType.isNil: return nil
      result.add(fieldType)
    return
  var head = n
  while head.kind in {nnkCall, nnkCommand, nnkBracketExpr} and head.len > 0:
    head = head[0]
  if head.kind == nnkIdent:
    let recordIndex = findHostRecord(records, $head)
    if recordIndex >= 0:
      let record = records[recordIndex]
      if record.isVariant:
        if record.hasDependentField or record.constructors.len == 0:
          return nil
        for mapping in mappings:
          if mapping.eponymName == $head:
            return mapping.nimType
        return nil
      if (record.hasDependentField and not record.trustDependentFields) or
          record.fields.len == 0:
        return nil
      let recordAllowsDependentFields = allowDependentSigma or
        record.trustDependentFields
      for field in record.fields:
        if runtimeNimType(field.eponymType, mappings, records,
                          recordAllowsDependentFields).isNil:
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

proc genericTypeUsedByStructuredSignature(decl: NimNode, name: string,
    mappings: seq[HostRuntimeType]): bool =
  ## Imported definitions do not have a Nim body AST from which to discover
  ## runtime uses of a generic type. When that type occurs beneath a supported
  ## structural codec in a signature, preserve its explicit runtime type
  ## witness so the wrapper can recursively apply the leaf codec.
  if decl.kind != nnkProcDef or decl[3].kind != nnkFormalParams:
    return false
  if decl.len <= 6 or decl[6].kind != nnkEmpty:
    return false
  for i in 0 ..< decl[3].len:
    let parameter = decl[3][i]
    let typeNode = if i == 0: parameter
      elif parameter.kind == nnkIdentDefs: parameter[^2]
      else: newEmptyNode()
    if typeNode.kind == nnkEmpty: continue
    var pending = @[typeNode]
    while pending.len > 0:
      let current = pending.pop()
      if not mentionsName(current, name): continue
      let head = runtimeTypeHead(current)
      if head.kind == nnkIdent and $head == "Sig":
        return true
      if head.kind == nnkIdent:
        for mapping in mappings:
          if mapping.eponymName == $head and
              (mapping.isRuntimeVector or mapping.isRuntimeList or
               mapping.isRuntimeOption or mapping.isRuntimeStructuredVariant):
            return true
      for child in current:
        pending.add(child)

proc runtimeStructuredCodecsExpr(mappings: seq[HostRuntimeType],
                                 records: seq[HostRecord]): NimNode =
  result = newNimNode(nnkBracket)
  for mapping in mappings:
    if mapping.isSynthetic: continue
    if mapping.isRuntimeVector or mapping.isRuntimeList or
        mapping.isRuntimeOption or mapping.isRuntimeVariant or
        mapping.isRuntimeStructuredVariant or
        findHostRecord(records, mapping.eponymName) >= 0:
      continue
    let mappedName = newLit(mapping.eponymName)
    if mapping.isRuntimeCodec:
      let codec = newCall(newTree(nnkBracketExpr,
        bindSym"runtimeStructuredCustomCodec", mapping.nimType),
        mappedName, copyNimTree(mapping.encoder), copyNimTree(mapping.decoder))
      result.add(codec)
    else:
      result.add(newCall(newTree(nnkBracketExpr,
        bindSym"runtimeStructuredHostCodec", mapping.nimType), mappedName))

proc rawRuntimeValueCheck(eponymType, value, globals: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]],
    mappings: seq[HostRuntimeType], records: seq[HostRecord]): NimNode

proc runtimeTypeValueExpr(n: NimNode, globals: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]]): NimNode

proc runtimePiTypeValueExpr(n, globals: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]]): NimNode =
  if n.kind notin {nnkCall, nnkObjConstr} or n.len < 3 or
      n[0].kind notin {nnkIdent, nnkSym} or $n[0] != "Pi":
    return nil
  var binders: seq[tuple[name: string, domain: NimNode]] = @[]
  for i in 1 ..< n.len - 1:
    let binder = n[i]
    if binder.kind != nnkExprColonExpr or binder.len != 2 or
        binder[0].kind notin {nnkIdent, nnkSym}:
      return nil
    binders.add(($binder[0], binder[1]))
  proc build(index: int,
      localOverrides: seq[tuple[name: string, value: NimNode]]): NimNode =
    let domain = runtimeTypeValueExpr(binders[index].domain, globals,
      localOverrides)
    if domain.isNil: return nil
    let argument = genSym(nskParam, "runtimePiArgument")
    var codomainOverrides = localOverrides
    codomainOverrides.add((binders[index].name, argument))
    let codomain = if index + 1 < binders.len:
      build(index + 1, codomainOverrides)
    else:
      runtimeTypeValueExpr(n[^1], globals, codomainOverrides)
    if codomain.isNil: return nil
    let callback = newProc(
      params = @[bindSym"Value",
        newIdentDefs(argument, bindSym"Value", newEmptyNode())],
      body = newStmtList(codomain))
    var priorArguments = newNimNode(nnkBracket)
    for override in localOverrides:
      priorArguments.add(copyNimTree(override.value))
    newCall(bindSym"runtimeDependentArrowType", domain, globals, callback,
      newTree(nnkPrefix, ident"@", priorArguments))
  build(0, overrides)

proc runtimeValueConversionExpr(eponymType, nimType, value: NimNode,
                               toValue: bool,
                               mappings: seq[HostRuntimeType],
                               records: seq[HostRecord],
                               globals: NimNode,
                               allowDependentSigma = false,
                               indexOverrides: seq[tuple[name: string,
                                 value: NimNode]] = @[]): NimNode =
  if eponymType.kind == nnkEmpty or
      (eponymType.kind == nnkIdent and $eponymType in ["void", "unitTy"]):
    if toValue:
      return newTree(nnkBlockExpr, newEmptyNode(), newStmtList(value,
        newCall(bindSym"vUnit")))
    return newCall(bindSym"validateRuntimeUnitValue", value)
  let procParts = runtimeProcParts(eponymType)
  if not procParts.resultType.isNil:
    let rawValueCallback = hasRawValuePragma(nimType)
    if rawValueCallback:
      var argValueSyms: seq[NimNode] = @[]
      var argSyms: seq[NimNode] = @[]
      for i, _ in procParts.argTypes:
        argValueSyms.add(genSym(nskParam, "rawCallbackValue" & $i))
        argSyms.add(genSym(nskParam, "rawCallbackArgument" & $i))
      if toValue:
        var callbackBody = newStmtList()
        var callbackIndexOverrides = indexOverrides
        for i, argType in procParts.argTypes:
          let check = rawRuntimeValueCheck(argType, argValueSyms[i], globals,
            callbackIndexOverrides, mappings, records)
          if not check.isNil: callbackBody.add(check)
          if procParts.argNames[i].len > 0:
            callbackIndexOverrides.add((procParts.argNames[i],
              argValueSyms[i]))
        var hostCall = newCall(value)
        for argSym in argValueSyms:
          hostCall.add(argSym)
        let hostResult = genSym(nskLet, "rawCallbackResult")
        callbackBody.add(newLetStmt(hostResult, hostCall))
        let resultCheck = rawRuntimeValueCheck(procParts.resultType,
          hostResult, globals, callbackIndexOverrides, mappings, records)
        if not resultCheck.isNil: callbackBody.add(resultCheck)
        callbackBody.add(hostResult)
        var callbackValue = newStmtList(callbackBody)
        if procParts.isNullary:
          let unitValue = genSym(nskParam, "rawCallbackUnit")
          let checkedUnit = newCall(bindSym"validateRuntimeUnitValue", unitValue)
          let hostCallback = newProc(params = @[bindSym"Value",
            newIdentDefs(unitValue, bindSym"Value", newEmptyNode())],
            body = newStmtList(checkedUnit, callbackValue))
          var callbackValue = newCall(bindSym"vHostFunc", hostCallback)
          let callbackType = runtimeTypeValueExpr(eponymType, globals,
            indexOverrides)
          if not callbackType.isNil:
            callbackValue = newCall(bindSym"setRuntimeHostFunctionType",
              callbackValue, callbackType, globals)
          return callbackValue
        for i in countdown(argValueSyms.high, 0):
          let hostCallback = newProc(params = @[bindSym"Value",
            newIdentDefs(argValueSyms[i], bindSym"Value", newEmptyNode())],
            body = newStmtList(callbackValue))
          callbackValue = newCall(bindSym"vHostFunc", hostCallback)
        let callbackType = runtimeTypeValueExpr(eponymType, globals,
          indexOverrides)
        if not callbackType.isNil:
          callbackValue = newCall(bindSym"setRuntimeHostFunctionType",
            callbackValue, callbackType, globals)
        return callbackValue
      var callbackArgs = newNimNode(nnkBracket)
      var formal: seq[NimNode] = @[bindSym"Value"]
      for argSym in argSyms:
        callbackArgs.add(argSym)
        formal.add(newIdentDefs(argSym, bindSym"Value", newEmptyNode()))
      if procParts.isNullary:
        callbackArgs.add(newCall(bindSym"vUnit"))
      var callbackBody = newStmtList()
      var callbackIndexOverrides = indexOverrides
      for i, argType in procParts.argTypes:
        let check = rawRuntimeValueCheck(argType, argSyms[i], globals,
          callbackIndexOverrides, mappings, records)
        if not check.isNil: callbackBody.add(check)
        if procParts.argNames[i].len > 0:
          callbackIndexOverrides.add((procParts.argNames[i], argSyms[i]))
      let applied = newCall(bindSym"callRuntimeValue", value,
        newTree(nnkPrefix, ident"@", callbackArgs))
      let resultCheck = rawRuntimeValueCheck(procParts.resultType, applied,
        globals, callbackIndexOverrides, mappings, records)
      if not resultCheck.isNil: callbackBody.add(resultCheck)
      callbackBody.add(applied)
      return newProc(params = formal, body = callbackBody)
    let resultNimType = runtimeNimType(procParts.resultType, mappings, records,
                                       allowDependentSigma)
    if resultNimType.isNil: return nil
    var argNimTypes: seq[NimNode] = @[]
    var argValueSyms: seq[NimNode] = @[]
    var argSyms: seq[NimNode] = @[]
    for i, argType in procParts.argTypes:
      let argNimType = runtimeNimType(argType, mappings, records,
                                      allowDependentSigma)
      if argNimType.isNil: return nil
      argNimTypes.add(argNimType)
      argValueSyms.add(genSym(nskParam, "runtimeCallbackValue" & $i))
      argSyms.add(genSym(nskParam, "runtimeCallbackArgument" & $i))
    if toValue:
      var decodedArgs: seq[NimNode] = @[]
      var callbackIndexOverrides = indexOverrides
      for i, argType in procParts.argTypes:
        let decodedArg = runtimeValueConversionExpr(argType, argNimTypes[i],
          argValueSyms[i], false, mappings, records, globals,
          allowDependentSigma, callbackIndexOverrides)
        if decodedArg.isNil: return nil
        decodedArgs.add(decodedArg)
        callbackIndexOverrides.add((procParts.argNames[i], decodedArg))
      var hostResult = newCall(value)
      for decodedArg in decodedArgs:
        hostResult.add(decodedArg)
      let encodedResult = runtimeValueConversionExpr(procParts.resultType,
        resultNimType, hostResult, true, mappings, records, globals,
        allowDependentSigma, callbackIndexOverrides)
      if encodedResult.isNil: return nil
      var callbackValue = encodedResult
      if procParts.isNullary:
        let unitValue = genSym(nskParam, "runtimeCallbackUnit")
        let checkedUnit = newCall(bindSym"validateRuntimeUnitValue", unitValue)
        let hostCallback = newProc(params = @[bindSym"Value",
          newIdentDefs(unitValue, bindSym"Value", newEmptyNode())],
          body = newStmtList(checkedUnit, callbackValue))
        var callbackValue = newCall(bindSym"vHostFunc", hostCallback)
        let callbackType = runtimeTypeValueExpr(eponymType, globals,
          indexOverrides)
        if not callbackType.isNil:
          callbackValue = newCall(bindSym"setRuntimeHostFunctionType",
            callbackValue, callbackType, globals)
        return callbackValue
      for i in countdown(argValueSyms.high, 0):
        let callbackBody = newStmtList(callbackValue)
        let hostCallback = newProc(params = @[bindSym"Value",
          newIdentDefs(argValueSyms[i], bindSym"Value", newEmptyNode())],
          body = callbackBody)
        callbackValue = newCall(bindSym"vHostFunc", hostCallback)
      let callbackType = runtimeTypeValueExpr(eponymType, globals,
        indexOverrides)
      if not callbackType.isNil:
        callbackValue = newCall(bindSym"setRuntimeHostFunctionType",
          callbackValue, callbackType, globals)
      return callbackValue
    var encodedArgs = newNimNode(nnkBracket)
    var formal: seq[NimNode] = @[resultNimType]
    var callbackIndexOverrides = indexOverrides
    for i, argType in procParts.argTypes:
      let encodedArg = runtimeValueConversionExpr(argType, argNimTypes[i],
        argSyms[i], true, mappings, records, globals, allowDependentSigma,
        callbackIndexOverrides)
      if encodedArg.isNil: return nil
      encodedArgs.add(encodedArg)
      formal.add(newIdentDefs(argSyms[i], argNimTypes[i], newEmptyNode()))
      callbackIndexOverrides.add((procParts.argNames[i], argSyms[i]))
    if procParts.isNullary:
      encodedArgs.add(newCall(bindSym"vUnit"))
    let applied = newCall(bindSym"callRuntimeValue", value,
      newTree(nnkPrefix, ident"@", encodedArgs))
    let decodedResult = runtimeValueConversionExpr(procParts.resultType,
      resultNimType, applied, false, mappings, records, globals,
      allowDependentSigma, callbackIndexOverrides)
    if decodedResult.isNil: return nil
    return newProc(params = formal, body = newStmtList(decodedResult))
  let typeHead = runtimeTypeHead(eponymType)
  if typeHead.kind == nnkIdent:
    for mapping in mappings:
      if mapping.isRuntimeCodec and mapping.eponymName == $typeHead:
        let codec = copyNimTree(if toValue: mapping.encoder else: mapping.decoder)
        let codecCall = newCall(codec, value, globals)
        let validatedValue = genSym(nskLet, "runtimeCodecValue")
        let valueToCheck = if toValue: validatedValue else: value
        let check = rawRuntimeValueCheck(eponymType, valueToCheck, globals,
          indexOverrides, mappings, records)
        if check.isNil: return codecCall
        var body = newStmtList()
        if toValue:
          body.add(newLetStmt(validatedValue, codecCall))
          body.add(check)
          body.add(validatedValue)
        else:
          body.add(check)
          body.add(codecCall)
        return newTree(nnkBlockExpr, newEmptyNode(), body)
      if eponymType.kind in {nnkIdent, nnkSym} and
          mapping.eponymName == $typeHead and not mapping.isSynthetic and
          not mapping.isRuntimeVector and not mapping.isRuntimeList and
          not mapping.isRuntimeOption and not mapping.isRuntimeVariant and
          not mapping.isRuntimeStructuredVariant and
          not mapping.isRuntimeIndexedType and
          findHostRecord(records, mapping.eponymName) < 0:
        let expectedType = runtimeTypeValueExpr(eponymType, globals,
          indexOverrides)
        if expectedType.isNil: return nil
        let converterSym = if toValue:
          bindSym"toHostValueAtRuntimeType"
        else:
          bindSym"valueToHostAtRuntimeType"
        return newCall(newTree(nnkBracketExpr, converterSym, nimType), value,
          expectedType, globals)
      if mapping.isRuntimeVariant and mapping.eponymName == $typeHead:
        let familyName = newLit(mapping.eponymName)
        let constructors = newCall(bindSym"runtimeVariantConstructorNames",
          globals, familyName)
        if toValue:
          return newCall(bindSym"runtimeVariantToValue", value, globals,
            familyName, constructors)
        return newCall(bindSym"valueToRuntimeVariant", value, globals,
          familyName, constructors)
      if mapping.isRuntimeStructuredVariant and
          mapping.eponymName == $typeHead:
        let familyName = newLit(mapping.eponymName)
        let constructors = newCall(bindSym"runtimeVariantConstructorNames",
          globals, familyName)
        if toValue:
          return newCall(bindSym"runtimeStructuredVariantToValue", value,
            globals, familyName, constructors,
            runtimeStructuredCodecsExpr(mappings, records))
        return newCall(bindSym"valueToRuntimeStructuredVariant", value,
          globals, familyName, constructors,
          runtimeStructuredCodecsExpr(mappings, records))
  for mapping in mappings:
    if mapping.isRuntimeVector:
      let vector = runtimeVectorComponents(eponymType, mapping.eponymName)
      if not vector.elementType.isNil:
        # Lower the original supported Nat grammar while substituting named
        # Sigma/record indices as Nim operands. This keeps Eponym `add`/`mul`
        # mapped to checked integer helpers even when an operand is a host
        # field or tuple projection.
        let expectedLength = runtimeNatIndexExpr(vector.length, indexOverrides)
        let elementNimType = runtimeNimType(vector.elementType, mappings,
          records, allowDependentSigma)
        if expectedLength.isNil or elementNimType.isNil: return nil
        let arrayLengthType = if mapping.isRuntimeVectorArray:
          runtimeArrayLengthTypeExpr(vector.length) else: nil
        if mapping.isRuntimeVectorArray and arrayLengthType.isNil: return nil
        let itemSym = genSym(nskParam, "runtimeVectorItem")
        let codecGlobalsSym = genSym(nskParam, "runtimeVectorGlobals")
        if toValue:
          let encodedItem = runtimeValueConversionExpr(vector.elementType,
            elementNimType, itemSym, true, mappings, records,
            codecGlobalsSym, allowDependentSigma, indexOverrides)
          if encodedItem.isNil: return nil
          let encoder = newProc(params = @[bindSym"Value",
            newIdentDefs(itemSym, elementNimType, newEmptyNode()),
            newIdentDefs(codecGlobalsSym, bindSym"Globals", newEmptyNode())],
            body = newStmtList(encodedItem))
          let encoderFn = if mapping.isRuntimeVectorArray:
            newTree(nnkBracketExpr, bindSym"arrayToVecValue",
              copyNimTree(arrayLengthType), copyNimTree(elementNimType))
          else: bindSym"seqToVecValue"
          return newCall(encoderFn, value, expectedLength, globals,
            newLit(mapping.eponymName), encoder)
        let decodedItem = runtimeValueConversionExpr(vector.elementType,
          elementNimType, itemSym, false, mappings, records,
          codecGlobalsSym, allowDependentSigma, indexOverrides)
        if decodedItem.isNil: return nil
        let decoder = newProc(params = @[elementNimType,
          newIdentDefs(itemSym, bindSym"Value", newEmptyNode()),
          newIdentDefs(codecGlobalsSym, bindSym"Globals", newEmptyNode())],
          body = newStmtList(decodedItem))
        let decoderFn = if mapping.isRuntimeVectorArray:
          newTree(nnkBracketExpr, bindSym"vecValueToArray",
            copyNimTree(arrayLengthType), copyNimTree(elementNimType))
        else: bindSym"vecValueToSeq"
        return newCall(decoderFn, value, expectedLength, globals,
          newLit(mapping.eponymName), decoder)
    elif mapping.isRuntimeList:
      let elementType = runtimeListElementType(eponymType, mapping.eponymName)
      if not elementType.isNil:
        let elementNimType = runtimeNimType(elementType, mappings, records,
          allowDependentSigma)
        if elementNimType.isNil: return nil
        let itemSym = genSym(nskParam, "runtimeListItem")
        let codecGlobalsSym = genSym(nskParam, "runtimeListGlobals")
        if toValue:
          let encodedItem = runtimeValueConversionExpr(elementType,
            elementNimType, itemSym, true, mappings, records,
            codecGlobalsSym, allowDependentSigma, indexOverrides)
          if encodedItem.isNil: return nil
          let encoder = newProc(params = @[bindSym"Value",
            newIdentDefs(itemSym, elementNimType, newEmptyNode()),
            newIdentDefs(codecGlobalsSym, bindSym"Globals", newEmptyNode())],
            body = newStmtList(encodedItem))
          return newCall(bindSym"seqToListValue", value, globals,
            newLit(mapping.eponymName), encoder)
        let decodedItem = runtimeValueConversionExpr(elementType,
          elementNimType, itemSym, false, mappings, records,
          codecGlobalsSym, allowDependentSigma, indexOverrides)
        if decodedItem.isNil: return nil
        let decoder = newProc(params = @[elementNimType,
          newIdentDefs(itemSym, bindSym"Value", newEmptyNode()),
          newIdentDefs(codecGlobalsSym, bindSym"Globals", newEmptyNode())],
          body = newStmtList(decodedItem))
        return newCall(bindSym"listValueToSeq", value, globals,
          newLit(mapping.eponymName), decoder)
    elif mapping.isRuntimeOption:
      let elementType = runtimeOptionElementType(eponymType,
        mapping.eponymName)
      if not elementType.isNil:
        let elementNimType = runtimeNimType(elementType, mappings, records,
          allowDependentSigma)
        if elementNimType.isNil: return nil
        let itemSym = genSym(nskParam, "runtimeOptionItem")
        let codecGlobalsSym = genSym(nskParam, "runtimeOptionGlobals")
        if toValue:
          let encodedItem = runtimeValueConversionExpr(elementType,
            elementNimType, itemSym, true, mappings, records,
            codecGlobalsSym, allowDependentSigma, indexOverrides)
          if encodedItem.isNil: return nil
          let encoder = newProc(params = @[bindSym"Value",
            newIdentDefs(itemSym, elementNimType, newEmptyNode()),
            newIdentDefs(codecGlobalsSym, bindSym"Globals", newEmptyNode())],
            body = newStmtList(encodedItem))
          return newCall(bindSym"optionToValue", value, globals,
            newLit(mapping.eponymName), encoder)
        let decodedItem = runtimeValueConversionExpr(elementType,
          elementNimType, itemSym, false, mappings, records,
          codecGlobalsSym, allowDependentSigma, indexOverrides)
        if decodedItem.isNil: return nil
        let decoder = newProc(params = @[elementNimType,
          newIdentDefs(itemSym, bindSym"Value", newEmptyNode()),
          newIdentDefs(codecGlobalsSym, bindSym"Globals", newEmptyNode())],
          body = newStmtList(decodedItem))
        return newCall(bindSym"valueToOption", value, globals,
          newLit(mapping.eponymName), decoder)
  let sigmaFields = runtimeSigmaFields(eponymType, allowDependentSigma)
  if sigmaFields.len >= 2:
    if nimType.kind notin {nnkTupleConstr, nnkTupleTy} or
        nimType.len != sigmaFields.len:
      return nil
    if toValue:
      var encodedFields: seq[NimNode] = @[]
      var fieldOverrides = indexOverrides
      for i, field in sigmaFields:
        let fieldValue = newTree(nnkBracketExpr, value, newLit(i))
        let encoded = runtimeValueConversionExpr(field.fieldType, nimType[i],
          fieldValue, true, mappings, records, globals, allowDependentSigma,
          fieldOverrides)
        if encoded.isNil: return nil
        encodedFields.add(encoded)
        if field.binder.len > 0:
          fieldOverrides.add((field.binder, fieldValue))
      result = encodedFields[^1]
      for i in countdown(encodedFields.high - 1, 0):
        result = newCall(bindSym"pairValue", encodedFields[i], result)
      return
    var current = copyNimTree(value)
    var decodedFields: seq[NimNode] = @[]
    var fieldOverrides = indexOverrides
    for i, field in sigmaFields:
      let fieldValue = if i < sigmaFields.high:
        newCall(bindSym"runtimePairFirst", current)
      else: current
      let decoded = runtimeValueConversionExpr(field.fieldType, nimType[i],
        fieldValue, false, mappings, records, globals, allowDependentSigma,
        fieldOverrides)
      if decoded.isNil: return nil
      decodedFields.add(decoded)
      if field.binder.len > 0:
        fieldOverrides.add((field.binder, decoded))
      if i < sigmaFields.high:
        current = newCall(bindSym"runtimePairSecond", current)
    result = newNimNode(nnkTupleConstr)
    for field in decodedFields: result.add(field)
    return
  if eponymType.kind == nnkIdent:
    let recordIndex = findHostRecord(records, $eponymType)
    if recordIndex >= 0:
      let record = records[recordIndex]
      if record.isVariant:
        if record.hasDependentField or record.constructors.len == 0:
          return nil
        var constructorNames = newNimNode(nnkBracket)
        for constructor in record.constructors:
          constructorNames.add(newLit(constructor))
        let namesSeq = newTree(nnkPrefix, ident"@", constructorNames)
        if toValue:
          return newCall(bindSym"enumToValue", value, globals, namesSeq)
        return newCall(newTree(nnkBracketExpr, bindSym"valueToEnum", nimType),
                       value, globals, namesSeq)
      if (record.hasDependentField and not record.trustDependentFields) or
          record.fields.len == 0:
        return nil
      let recordAllowsDependentFields = allowDependentSigma or
        record.trustDependentFields
      if toValue:
        var convertedFields: seq[NimNode] = @[]
        var indexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
        for field in record.fields:
          let fieldType = runtimeNimType(field.eponymType, mappings, records,
                                         recordAllowsDependentFields)
          if fieldType.isNil: return nil
          let fieldValue = newTree(nnkDotExpr, value, ident(field.name))
          let converted = runtimeValueConversionExpr(field.eponymType,
            fieldType, fieldValue, true, mappings, records, globals,
            recordAllowsDependentFields, indexOverrides)
          if converted.isNil: return nil
          convertedFields.add(converted)
          indexOverrides.add((field.name, fieldValue))
        var tail = newCall(bindSym"unitValue")
        for i in countdown(convertedFields.high, 0):
          tail = newCall(bindSym"pairValue", convertedFields[i], tail)
        return tail
      var current = value
      var fields = newNimNode(nnkObjConstr)
      fields.add(nimType)
      var decodeBody = newStmtList()
      var indexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
      for field in record.fields:
        let fieldType = runtimeNimType(field.eponymType, mappings, records,
                                       recordAllowsDependentFields)
        if fieldType.isNil: return nil
        let fieldSym = genSym(nskLet, field.name)
        let converted = runtimeValueConversionExpr(field.eponymType,
          fieldType, newCall(bindSym"runtimePairFirst", current), false,
          mappings, records, globals, recordAllowsDependentFields,
          indexOverrides)
        if converted.isNil: return nil
        decodeBody.add(newLetStmt(fieldSym, converted))
        fields.add(newTree(nnkExprColonExpr, ident(field.name), fieldSym))
        indexOverrides.add((field.name, fieldSym))
        current = newCall(bindSym"runtimePairSecond", current)
      decodeBody.add(fields)
      return newBlockStmt(decodeBody)
  var genericTypeBody = false
  if eponymType.kind == nnkIdent:
    for mapping in mappings:
      if mapping.isSynthetic and mapping.isGenericTypeBody and
          mapping.eponymName == $eponymType:
        genericTypeBody = true
        break
  if genericTypeBody:
    var whenBranches = newNimNode(nnkWhenStmt)
    for mapping in mappings:
      if not mapping.isOpaqueRuntimeType and not mapping.isRuntimeCodec:
        continue
      if mapping.isRuntimeIndexedType: continue
      let condition = newTree(nnkInfix, ident"is", copyNimTree(nimType),
                              copyNimTree(mapping.nimType))
      let mappedValue = runtimeValueConversionExpr(
        ident(mapping.eponymName), mapping.nimType, value, toValue, mappings,
        records, globals, allowDependentSigma, indexOverrides)
      if mappedValue.isNil: return nil
      whenBranches.add(newTree(nnkElifBranch, condition,
                               newStmtList(mappedValue)))
    let errorMessage = newLit("generic Nim type '" & repr(nimType) &
      "' has no runtimeType/runtimeCodec mapping")
    whenBranches.add(newTree(nnkElse, newStmtList(newTree(nnkPragma,
      newTree(nnkExprColonExpr, ident"error", errorMessage)))))
    var mappedValue = newNimNode(nnkBlockExpr)
    mappedValue.add(newEmptyNode())
    mappedValue.add(newStmtList(whenBranches))
    return mappedValue
  let valueFn = runtimeValueConverter(eponymType, nimType, toValue, records)
  if valueFn.isNil: return nil
  if simpleRuntimeCodec(eponymType) == "bool":
    return newCall(valueFn, value, globals)
  if simpleRuntimeCodec(eponymType) == "nat" and toValue:
    return newCall(bindSym"natToValue", value, globals)
  if simpleRuntimeCodec(eponymType) == "nat" and not toValue:
    return newCall(bindSym"valueToNat", value, globals)
  newCall(valueFn, value)

proc genericRuntimeInfo(decl: NimNode,
                        mappings: seq[HostRuntimeType],
                        allowUnmappedValue = false): tuple[
    genericParams: NimNode, typeNames: seq[string],
    genericNames: seq[NimNode], genericNatArgs: seq[bool],
    genericBoolArgs: seq[bool], genericIntArgs: seq[bool],
    genericValueArgs: seq[bool], genericTypeBodyArgs: seq[bool],
    genericValueTypeNames: seq[string],
    genericValueTypeExprs: seq[NimNode],
    genericMappedTypes: seq[NimNode], genericMappedNimTypes: seq[NimNode],
    codecMappings: seq[HostRuntimeType], error: string] =
  result.genericParams = newEmptyNode()
  result.codecMappings = mappings
  if decl[2].kind == nnkEmpty:
    return
  result.genericParams = newNimNode(nnkGenericParams)
  for param in decl[2]:
    if param.kind != nnkIdentDefs or param[^2].kind == nnkEmpty:
      result.error = "runtime wrappers require explicitly typed generic binders"
      return
    let binderType = nimTypeToEponym(param[^2])
    let binderTypeHead = runtimeTypeHead(param[^2])
    let binderTypeHeadName = if binderTypeHead.kind == nnkIdent:
      $binderTypeHead else: ""
    var mappedBinder: HostRuntimeType
    var hasMappedBinder = false
    for mapping in mappings:
      if mapping.eponymName == binderType or
          mapping.eponymName == binderTypeHeadName:
        mappedBinder = mapping
        hasMappedBinder = true
        break
    if binderType notin ["Type 0", "Nat", "Bool", "Int"] and
        not hasMappedBinder and not allowUnmappedValue:
      result.error = "runtime wrappers currently support only type-level " &
        "binders annotated with Univ, primitive value indices, or values " &
        "with an explicit runtimeType mapping"
      return
    for i in 0 ..< param.len - 2:
      let name = $param[i]
      if name in result.genericNames.mapIt($it):
        result.error = "duplicate generic runtime parameter '" & name & "'"
        return
      let typeUsedByBody = binderType == "Type 0" and
        ((decl.len > 6 and not decl[6].isNil and
          mentionsName(decl[6], name)) or
         genericTypeUsedByStructuredSignature(decl, name, mappings))
      if typeUsedByBody:
        var representedTypes: seq[string] = @[]
        for mapping in mappings:
          if mapping.isRuntimeIndexedType or
              (not mapping.isOpaqueRuntimeType and not mapping.isRuntimeCodec) or
              mapping.isRuntimeVector or mapping.isRuntimeList or
              mapping.isRuntimeOption or mapping.isRuntimeVariant or
              mapping.isRuntimeStructuredVariant:
            continue
          if not mapping.isRuntimeCodec and mapping.nimType.kind == nnkIdent and
              $mapping.nimType == "seq":
            continue
          let mappedNimName = repr(mapping.nimType)
          if mappedNimName in representedTypes:
            result.error = "generic type parameter '" & name &
              "' is used by the runtime body, but Nim type '" &
              mappedNimName & "' has ambiguous runtime type mappings"
            return
          representedTypes.add(mappedNimName)
        if representedTypes.len == 0:
          result.error = "generic type parameter '" & name &
            "' is used by the runtime body; add a runtimeType mapping for " &
            "its opaque Nim type"
          return
      let genericName = copyNimTree(param[i])
      result.genericNames.add(genericName)
      result.genericMappedTypes.add(nil)
      result.genericMappedNimTypes.add(nil)
      result.genericValueArgs.add(false)
      result.genericTypeBodyArgs.add(typeUsedByBody)
      result.genericValueTypeNames.add("")
      result.genericValueTypeExprs.add(copyNimTree(param[^2]))
      if binderType == "Type 0":
        result.typeNames.add(name)
        result.genericParams.add(newIdentDefs(copyNimTree(param[i]),
          newEmptyNode(), newEmptyNode()))
        result.genericNatArgs.add(false)
        result.genericBoolArgs.add(false)
        result.genericIntArgs.add(false)
        result.codecMappings.add(HostRuntimeType(eponymName: name,
          nimType: copyNimTree(param[i]), isSynthetic: true,
          isGenericTypeBody: typeUsedByBody))
      elif binderType == "Nat":
        let staticInt = newTree(nnkBracketExpr, ident"static", ident"int")
        result.genericParams.add(newIdentDefs(copyNimTree(param[i]), staticInt,
          newEmptyNode()))
        result.genericNatArgs.add(true)
        result.genericBoolArgs.add(false)
        result.genericIntArgs.add(false)
      elif binderType == "Bool":
        let staticBool = newTree(nnkBracketExpr, ident"static", ident"bool")
        result.genericParams.add(newIdentDefs(copyNimTree(param[i]), staticBool,
          newEmptyNode()))
        result.genericNatArgs.add(false)
        result.genericBoolArgs.add(true)
        result.genericIntArgs.add(false)
      elif binderType == "Int":
        let staticInt = newTree(nnkBracketExpr, ident"static", ident"int")
        result.genericParams.add(newIdentDefs(copyNimTree(param[i]), staticInt,
          newEmptyNode()))
        result.genericNatArgs.add(false)
        result.genericBoolArgs.add(false)
        result.genericIntArgs.add(true)
      else:
        if hasMappedBinder:
          let staticMapped = newTree(nnkBracketExpr, ident"static",
                                     copyNimTree(mappedBinder.nimType))
          result.genericParams.add(newIdentDefs(copyNimTree(param[i]),
            staticMapped, newEmptyNode()))
          result.genericNatArgs.add(false)
          result.genericBoolArgs.add(false)
          result.genericIntArgs.add(false)
          result.genericMappedTypes[^1] = copyNimTree(param[^2])
          result.genericMappedNimTypes[^1] = copyNimTree(mappedBinder.nimType)
          continue
        result.genericParams.add(newIdentDefs(copyNimTree(param[i]), bindSym"Value",
          newEmptyNode()))
        result.genericNatArgs.add(false)
        result.genericBoolArgs.add(false)
        result.genericIntArgs.add(false)
        result.genericValueArgs[^1] = true
        result.genericValueTypeNames[^1] = binderType

proc genericRuntimeValueArgs(generic: tuple[genericParams: NimNode,
    typeNames: seq[string], genericNames: seq[NimNode],
    genericNatArgs: seq[bool], genericBoolArgs: seq[bool],
    genericIntArgs: seq[bool], genericValueArgs: seq[bool],
    genericTypeBodyArgs: seq[bool],
    genericValueTypeNames: seq[string],
    genericValueTypeExprs: seq[NimNode],
    genericMappedTypes: seq[NimNode], genericMappedNimTypes: seq[NimNode],
    codecMappings: seq[HostRuntimeType],
    error: string], globals: NimNode, mappings: seq[HostRuntimeType],
    records: seq[HostRecord]): seq[NimNode] =
  for i, genericName in generic.genericNames:
    if generic.genericNatArgs[i]:
      result.add(newCall(bindSym"natToValue", copyNimTree(genericName),
                         globals))
    elif generic.genericBoolArgs[i]:
      result.add(newCall(bindSym"boolToValue", copyNimTree(genericName),
                         globals))
    elif generic.genericIntArgs[i]:
      result.add(newCall(bindSym"intToValue", copyNimTree(genericName)))
    elif generic.genericTypeBodyArgs[i]:
      var whenBranches = newNimNode(nnkWhenStmt)
      for mapping in mappings:
        if mapping.isRuntimeIndexedType or
            (not mapping.isOpaqueRuntimeType and not mapping.isRuntimeCodec) or
            mapping.isRuntimeVector or mapping.isRuntimeList or
            mapping.isRuntimeOption or mapping.isRuntimeVariant or
            mapping.isRuntimeStructuredVariant:
          continue
        if not mapping.isRuntimeCodec and mapping.nimType.kind == nnkIdent and
            $mapping.nimType == "seq":
          continue
        let condition = newTree(nnkInfix, ident"is",
          copyNimTree(genericName), copyNimTree(mapping.nimType))
        let value = newCall(bindSym"runtimeGlobalValue", globals,
                            newLit(mapping.eponymName))
        whenBranches.add(newTree(nnkElifBranch, condition, newStmtList(value)))
      let errorMessage = newLit("generic Nim type '" & $genericName &
        "' has no runtimeType mapping")
      whenBranches.add(newTree(nnkElse, newStmtList(newTree(nnkPragma,
        newTree(nnkExprColonExpr, ident"error", errorMessage)))))
      var mappedTypeValue = newNimNode(nnkBlockExpr)
      mappedTypeValue.add(newEmptyNode())
      mappedTypeValue.add(newStmtList(whenBranches))
      result.add(mappedTypeValue)
    elif not generic.genericMappedTypes[i].isNil:
      let encoded = runtimeValueConversionExpr(
        generic.genericMappedTypes[i], generic.genericMappedNimTypes[i],
        copyNimTree(genericName), true, mappings, records, globals)
      if encoded.isNil:
        error("generic runtime value needs a codec for Eponym type '" &
          repr(generic.genericMappedTypes[i]) & "'")
      result.add(encoded)
    else:
      result.add(newCall(bindSym"vType", newLit(0)))

proc bindingCall(binding: HostPostulateBinding, bindingsSym, globalsSym: NimNode,
                 mappings: seq[HostRuntimeType],
                 records: seq[HostRecord]): NimNode =
  let nameLit = newLit(binding.postulateName)
  if binding.rawValue:
    return newCall(bindSym"bindHostValueNary", bindingsSym, globalsSym,
                   nameLit, binding.implementation)
  if binding.pairResult:
    let pairType = if not binding.pairResultType.isNil:
      copyNimTree(binding.pairResultType)
    else:
      newCall(ident"Sig",
        ident(binding.eponymTypes[binding.pairArgCount]),
        ident(binding.eponymTypes[binding.pairArgCount + 1]))
    let pairNimType = runtimeNimType(pairType, mappings, records,
                                    binding.trustedPairIndex)
    if pairNimType.isNil:
      error("bindPostulatePair needs runtime codecs for both pair fields")
    var runtimeArgs: seq[NimNode] = @[]
    var decodedArgs: seq[NimNode] = @[]
    var adapterBody = newStmtList()
    var pairIndexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
    for i in 0 ..< binding.pairArgCount:
      let eponymArgType = ident(binding.eponymTypes[i])
      let nimArgType = runtimeNimType(eponymArgType, mappings, records)
      if nimArgType.isNil:
        error("bindPostulatePair needs a runtime codec for argument '" &
          binding.eponymTypes[i] & "'")
      let runtimeArg = genSym(nskParam, "runtimeArgument")
      runtimeArgs.add(runtimeArg)
      let decoded = runtimeValueConversionExpr(eponymArgType, nimArgType,
        runtimeArg, false, mappings, records, globalsSym)
      if decoded.isNil:
        error("bindPostulatePair could not build an argument codec")
      let decodedArg = genSym(nskVar, "hostPairArgument")
      adapterBody.add(newVarStmt(decodedArg, decoded))
      decodedArgs.add(decodedArg)
      if i < binding.pairResultArgNames.len and
          binding.pairResultArgNames[i].len > 0:
        pairIndexOverrides.add((binding.pairResultArgNames[i], decodedArg))
    let hostResult = genSym(nskLet, "hostPairResult")
    let encodedResult = runtimeValueConversionExpr(pairType, pairNimType,
      hostResult, true, mappings, records, globalsSym,
      binding.trustedPairIndex, pairIndexOverrides)
    if encodedResult.isNil:
      error("bindPostulatePair could not build a value codec")
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
  var adapterTypes = binding.eponymTypeExprs
  if adapterTypes.len == 0:
    for typeName in binding.eponymTypes:
      adapterTypes.add(ident(typeName))
  if adapterTypes.len == 1:
    adapterTypes = @[adapterTypes[0], adapterTypes[0]]
  # Explicit type arguments have always used the general typed codec path,
  # which also supports var parameters. Preserve that for simple identifiers
  # while allowing applied structural types in the same path.
  var needsGeneralCodec = adapterTypes.len > 0
  for typeExpr in adapterTypes:
    if typeExpr.kind != nnkIdent: needsGeneralCodec = true
    let typeHead = runtimeTypeHead(typeExpr)
    for mapping in mappings:
      if mapping.isRuntimeCodec and not typeHead.isNil and
          typeHead.kind == nnkIdent and mapping.eponymName == $typeHead:
        needsGeneralCodec = true
  if needsGeneralCodec and adapterTypes.len > 0:
    let argumentCount = adapterTypes.len - 1
    var decodedArgs: seq[NimNode] = @[]
    var adapterBody = newStmtList()
    var indexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
    for i in 0 ..< argumentCount:
      let eponymType = adapterTypes[i]
      let nimType = runtimeNimType(eponymType, mappings, records)
      if nimType.isNil:
        error("bindPostulate for '" & binding.postulateName &
          "' needs a runtime codec for argument type '" &
          repr(eponymType) & "'")
      let decoded = runtimeValueConversionExpr(eponymType, nimType,
        newTree(nnkBracketExpr, ident"runtimeArguments", newLit(i)), false,
        mappings, records, ident"runtimeGlobals", false, indexOverrides)
      if decoded.isNil:
        error("bindPostulate could not build a runtime codec for argument '" &
          repr(adapterTypes[i]) & "'")
      let decodedArg = genSym(nskVar, "hostArgument" & $i)
      adapterBody.add(newVarStmt(decodedArg, decoded))
      decodedArgs.add(decodedArg)
      if i < binding.eponymArgumentNames.len and
          binding.eponymArgumentNames[i].len > 0 and
          binding.eponymArgumentNames[i] != "_":
        indexOverrides.add((binding.eponymArgumentNames[i], decodedArg))
    let resultEponymType = adapterTypes[^1]
    let resultNimType = runtimeNimType(resultEponymType, mappings, records)
    if resultNimType.isNil:
      error("bindPostulate for '" & binding.postulateName &
        "' needs a runtime codec for result type '" &
        repr(resultEponymType) & "'")
    var implementationCall = newCall(binding.implementation)
    for decodedArg in decodedArgs:
      implementationCall.add(decodedArg)
    let encodedResult = runtimeValueConversionExpr(resultEponymType,
      resultNimType, implementationCall, true, mappings, records,
      ident"runtimeGlobals", false, indexOverrides)
    if encodedResult.isNil:
      error("bindPostulate could not build a runtime codec for result '" &
        repr(adapterTypes[^1]) & "'")
    let runtimeArgsSym = ident"runtimeArguments"
    let runtimeGlobalsSym = ident"runtimeGlobals"
    adapterBody.add(encodedResult)
    let adapter = newProc(params = @[bindSym"Value",
      newIdentDefs(runtimeArgsSym,
        newTree(nnkBracketExpr, ident"seq", bindSym"Value"), newEmptyNode()),
      newIdentDefs(runtimeGlobalsSym, bindSym"Globals", newEmptyNode())],
      body = adapterBody)
    return newCall(bindSym"bindHostValueNary", bindingsSym, globalsSym,
      nameLit, adapter)
  if binding.eponymTypes.len == 0:
    return newCall(bindSym"bindHostIntUnary", bindingsSym, globalsSym,
                   nameLit, binding.implementation)
  var typeIndexes: seq[int] = @[]
  if binding.eponymTypes.len == 2 and binding.eponymTypes[1] == "Nat":
    typeIndexes = @[0]
  elif binding.eponymTypes.len == 2:
    typeIndexes = @[0, 1]
  elif binding.eponymTypes.len == 3 and binding.eponymTypes[0] == "Nat":
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
  let adapter =
    if binding.eponymTypes.len == 1: bindSym"bindHostOpaqueUnary"
    elif binding.eponymTypes.len == 2 and binding.eponymTypes[1] == "Nat":
      bindSym"bindHostOpaqueNatUnary"
    elif binding.eponymTypes.len == 2: bindSym"bindHostOpaqueMapUnary"
    elif binding.eponymTypes.len == 3 and binding.eponymTypes[0] == "Nat":
      bindSym"bindHostNatOpaqueMapBinary"
    elif binding.eponymTypes.len == 3: bindSym"bindHostOpaqueBinary"
    elif binding.eponymTypes.len == 4: bindSym"bindHostOpaqueTernary"
    elif binding.eponymTypes.len == 5: bindSym"bindHostOpaqueQuaternary"
    elif binding.eponymTypes.len == 6: bindSym"bindHostOpaqueQuinary"
    else:
      error("unsupported bindPostulate codec combination for '" &
            binding.postulateName & "'")
  var genericAdapter = newNimNode(nnkBracketExpr)
  genericAdapter.add(adapter)
  for typeArg in typeArgs:
    genericAdapter.add(typeArg)
  var call = newCall(genericAdapter, bindingsSym, globalsSym, nameLit)
  if binding.eponymTypes.len == 2 and binding.eponymTypes[1] == "Nat":
    call.add(newLit(binding.eponymTypes[0]))
  elif binding.eponymTypes.len == 3 and binding.eponymTypes[0] == "Nat":
    call.add(newLit(binding.eponymTypes[1]))
    call.add(newLit(binding.eponymTypes[2]))
  else:
    for eponymName in binding.eponymTypes:
      call.add(newLit(eponymName))
  call.add(binding.implementation)
  call

proc unsupportedRuntimeWrapper(decl: NimNode, defName: string,
                               mappings: seq[HostRuntimeType],
                               records: seq[HostRecord],
                               allowDependentSigma = false): NimNode =
  let params = decl[3]
  var reason = "unsupported generic or higher-order signature"
  let generic = genericRuntimeInfo(decl, mappings)
  let codecMappings = if generic.error.len == 0:
    generic.codecMappings else: mappings
  if generic.error.len > 0:
    reason = generic.error
  elif params.len == 0 or params[0].kind == nnkEmpty:
    reason = "Eponym procedure has no explicit runtime result type"
  elif runtimeNimType(params[0], codecMappings, records,
                      allowDependentSigma).isNil:
    reason = "no runtime codec for Eponym result type '" & repr(params[0]) & "'"
  else:
    for i in 1 ..< params.len:
      let p = params[i]
      if p.kind != nnkIdentDefs:
        reason = "unsupported Nim parameter declaration for Eponym procedure '" &
          defName & "'"
        break
      if runtimeNimType(p[^2], codecMappings, records,
                        allowDependentSigma).isNil:
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
                         records: seq[HostRecord],
                         allowDependentSigma = false): NimNode =
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
  let resultType = runtimeNimType(params[0], codecMappings, records,
                                  allowDependentSigma)
  if resultType.isNil: return nil

  var formal = newNimNode(nnkFormalParams)
  formal.add(ident("int"))
  var argSyms: seq[NimNode] = @[]
  var argNames: seq[string] = @[]
  var argEponymTypes: seq[NimNode] = @[]
  var argNimTypes: seq[NimNode] = @[]
  for i in 1 ..< params.len:
    let p = params[i]
    if p.kind != nnkIdentDefs: return nil
    let argType = runtimeNimType(p[^2], codecMappings, records,
                                 allowDependentSigma)
    if argType.isNil: return nil
    for j in 0 ..< p.len - 2:
      let argName = if p[j].kind == nnkPragmaExpr: p[j][0] else: p[j]
      let argSym = genSym(nskParam, $argName)
      formal.add(newIdentDefs(argSym, argType, newEmptyNode()))
      argSyms.add(argSym)
      argNames.add($argName)
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
      wrapperBody.add(bindingCall(binding, bindingSym, globalsSym, codecMappings,
                                  records))

  var values = newNimNode(nnkBracket)
  for genericArg in genericRuntimeValueArgs(generic, globalsSym,
      codecMappings, records):
    values.add(genericArg)
  if hasImportedNullaryUnitArgument(decl):
    values.add(newCall(bindSym"vUnit"))
  var wrapperIndexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
  for i, argSym in argSyms:
    values.add(runtimeValueConversionExpr(argEponymTypes[i], argNimTypes[i],
      argSym, true, codecMappings, records, globalsSym,
      allowDependentSigma, wrapperIndexOverrides))
    if values[^1].isNil: return nil
    wrapperIndexOverrides.add((argNames[i], argSym))
  let valuesSeq = newTree(nnkPrefix, ident("@"), values)
  var callArgs = @[dirLit, srcLit, nameLit, valuesSeq]
  if not bindingSym.isNil: callArgs.add(bindingSym)
  let runtimeValue = genSym(nskLet, "runtimeValue")
  wrapperBody.add(newLetStmt(runtimeValue,
    newCall(bindSym"callValueFuncDir", callArgs)))
  let resultExpr = runtimeValueConversionExpr(params[0], resultType,
    runtimeValue, false, codecMappings, records, globalsSym,
    allowDependentSigma, wrapperIndexOverrides)
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

proc runtimeTypeValueExpr(n: NimNode, globals: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]]): NimNode =
  if n.isNil: return nil
  if n.kind in {nnkCall, nnkObjConstr} and n.len > 0 and
      n[0].kind in {nnkIdent, nnkSym} and $n[0] == "Pi":
    return runtimePiTypeValueExpr(n, globals, overrides)
  if n.kind == nnkInfix and n.len == 3 and $n[0] == "->":
    let domain = runtimeTypeValueExpr(n[1], globals, overrides)
    let codomain = runtimeTypeValueExpr(n[2], globals, overrides)
    if domain.isNil or codomain.isNil: return nil
    return newCall(bindSym"runtimeArrowType", domain, codomain)
  if n.kind in {nnkIdent, nnkSym}:
    if overrides.len > 0:
      for i in countdown(overrides.high, 0):
        if $n == overrides[i].name:
          return copyNimTree(overrides[i].value)
    return newCall(bindSym"runtimeGlobalValue", globals, newLit($n))
  if n.kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                nnkInt64Lit}:
    if n.intVal < 0: return newCall(bindSym"intToValue", newLit(n.intVal))
    return newCall(bindSym"natToValue", newLit(n.intVal), globals)
  if n.kind == nnkPrefix and n.len == 2 and $n[0] == "-" and
      n[1].kind in {nnkIntLit, nnkInt8Lit, nnkInt16Lit, nnkInt32Lit,
                    nnkInt64Lit}:
    return newCall(bindSym"intToValue", newLit(-n[1].intVal))
  if n.kind == nnkPar and n.len == 1:
    return runtimeTypeValueExpr(n[0], globals, overrides)
  if n.kind in {nnkCall, nnkCommand, nnkBracketExpr, nnkObjConstr,
                nnkInfix} and n.len >= 2:
    let fnNode = if n.kind == nnkInfix:
      ident($n[0]) else: n[0]
    let fnValue = runtimeTypeValueExpr(fnNode, globals, overrides)
    if fnValue.isNil: return nil
    var args = newNimNode(nnkBracket)
    let firstArg = if n.kind == nnkInfix: 1 else: 1
    for i in firstArg ..< n.len:
      let argValue = runtimeTypeValueExpr(n[i], globals, overrides)
      if argValue.isNil: return nil
      args.add(argValue)
    return newCall(bindSym"callRuntimeValue", fnValue,
      newTree(nnkPrefix, ident"@", args))
  nil

proc rawRuntimeTypeCheckable(eponymType: NimNode,
    mappings: seq[HostRuntimeType], records: seq[HostRecord]): bool =
  if eponymType.isNil: return false
  for mapping in mappings:
    if mapping.isRuntimeCodec or mapping.isRuntimeVector or
        mapping.isRuntimeList or mapping.isRuntimeOption or
        mapping.isRuntimeVariant or mapping.isRuntimeStructuredVariant:
      continue
    if findHostRecord(records, mapping.eponymName) >= 0: continue
    if mentionsName(eponymType, mapping.eponymName): return false
  true

proc rawRuntimePairValueCheck(firstType, secondType, value, globals: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]],
    mappings: seq[HostRuntimeType], records: seq[HostRecord],
    binderName = ""): NimNode =
  let first = genSym(nskLet, "rawPairFirst")
  let second = genSym(nskLet, "rawPairSecond")
  let firstCheck = rawRuntimeValueCheck(firstType, first, globals, overrides,
    mappings, records)
  var secondOverrides = overrides
  if binderName.len > 0: secondOverrides.add((binderName, first))
  let secondCheck = rawRuntimeValueCheck(secondType, second, globals,
    secondOverrides, mappings, records)
  if firstCheck.isNil or secondCheck.isNil: return nil
  result = newStmtList()
  result.add(newLetStmt(first, newCall(bindSym"runtimePairFirst",
    copyNimTree(value))))
  result.add(firstCheck)
  result.add(newLetStmt(second, newCall(bindSym"runtimePairSecond",
    copyNimTree(value))))
  result.add(secondCheck)

proc rawRuntimeRecordValueCheck(record: HostRecord, value, globals: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]],
    mappings: seq[HostRuntimeType], records: seq[HostRecord]): NimNode =
  var current = copyNimTree(value)
  var fieldOverrides = overrides
  result = newStmtList()
  for field in record.fields:
    let fieldValue = genSym(nskLet, "rawRecordField")
    result.add(newLetStmt(fieldValue, newCall(bindSym"runtimePairFirst",
      current)))
    let check = rawRuntimeValueCheck(field.eponymType, fieldValue, globals,
      fieldOverrides, mappings, records)
    if check.isNil: return nil
    result.add(check)
    fieldOverrides.add((field.name, fieldValue))
    current = newCall(bindSym"runtimePairSecond", current)
  result.add(newCall(bindSym"validateRuntimeUnitValue", current))

proc rawRuntimeValueCheck(eponymType, value, globals: NimNode,
    overrides: seq[tuple[name: string, value: NimNode]],
    mappings: seq[HostRuntimeType], records: seq[HostRecord]): NimNode =
  let typeHead = runtimeTypeHead(eponymType)
  if typeHead.kind == nnkIdent:
    let recordIndex = findHostRecord(records, $typeHead)
    if recordIndex >= 0 and not records[recordIndex].isVariant:
      return rawRuntimeRecordValueCheck(records[recordIndex], value, globals,
        overrides, mappings, records)
  let sigma = runtimeSigmaComponents(eponymType, allowDependent = true)
  if not sigma.first.isNil:
    return rawRuntimePairValueCheck(sigma.first, sigma.second, value, globals,
      overrides, mappings, records, sigma.binder)
  if typeHead.kind == nnkIdent:
    for mapping in mappings:
      if mapping.eponymName != $typeHead or mapping.isSynthetic or
          mapping.isRuntimeCodec or mapping.isRuntimeVector or
          mapping.isRuntimeList or mapping.isRuntimeOption or
          mapping.isRuntimeVariant or mapping.isRuntimeStructuredVariant or
          findHostRecord(records, mapping.eponymName) >= 0:
        continue
      let expectedType = runtimeTypeValueExpr(eponymType, globals, overrides)
      if expectedType.isNil: return nil
      return newCall(bindSym"validateRuntimeRawValue", copyNimTree(value),
        expectedType, copyNimTree(globals),
        runtimeStructuredCodecsExpr(mappings, records))
  for mapping in mappings:
    if mapping.isRuntimeList:
      let elementType = runtimeListElementType(eponymType,
        mapping.eponymName)
      if elementType.isNil: continue
      let expectedType = runtimeTypeValueExpr(elementType, globals, overrides)
      if expectedType.isNil: return nil
      return newCall(bindSym"validateRuntimeListRawValue",
        copyNimTree(value), expectedType, copyNimTree(globals),
        newLit(mapping.eponymName), runtimeStructuredCodecsExpr(mappings,
          records))
    if mapping.isRuntimeOption:
      let elementType = runtimeOptionElementType(eponymType,
        mapping.eponymName)
      if elementType.isNil: continue
      let expectedType = runtimeTypeValueExpr(elementType, globals, overrides)
      if expectedType.isNil: return nil
      return newCall(bindSym"validateRuntimeOptionRawValue",
        copyNimTree(value), expectedType, copyNimTree(globals),
        newLit(mapping.eponymName), runtimeStructuredCodecsExpr(mappings,
          records))
    if not mapping.isRuntimeVector: continue
    let vector = runtimeVectorComponents(eponymType, mapping.eponymName)
    if vector.elementType.isNil: continue
    let elementType = runtimeTypeValueExpr(vector.elementType, globals,
      overrides)
    var natOverrides: seq[tuple[name: string, value: NimNode]] = @[]
    for override in overrides:
      natOverrides.add((override.name, newCall(bindSym"valueToNat",
        copyNimTree(override.value), copyNimTree(globals))))
    let expectedLength = runtimeNatIndexExpr(vector.length, natOverrides)
    if elementType.isNil or expectedLength.isNil: return nil
    return newCall(bindSym"validateRuntimeVectorRawValue",
      copyNimTree(value), elementType, expectedLength, copyNimTree(globals),
      newLit(mapping.eponymName), runtimeStructuredCodecsExpr(mappings,
        records))
  if not rawRuntimeTypeCheckable(eponymType, mappings, records): return nil
  let expectedType = runtimeTypeValueExpr(eponymType, globals, overrides)
  if expectedType.isNil: return nil
  newCall(bindSym"validateRuntimeRawValue", copyNimTree(value),
    expectedType, copyNimTree(globals), runtimeStructuredCodecsExpr(mappings,
      records))

proc hasTypedGenericCallback(decl: NimNode,
    mappings: seq[HostRuntimeType], records: seq[HostRecord],
    allowDependentSigma: bool): bool =
  let generic = genericRuntimeInfo(decl, mappings, allowUnmappedValue = true)
  if generic.error.len > 0: return false
  for i, isValue in generic.genericValueArgs:
    if not isValue: continue
    let nimType = runtimeNimType(generic.genericValueTypeExprs[i],
      generic.codecMappings, records, allowDependentSigma)
    if not nimType.isNil and nimType.kind == nnkProcTy: return true

proc dynamicGenericRuntimeWrapper(decl: NimNode, baseDir, src,
    defName: string, bindings: seq[HostPostulateBinding],
    mappings: seq[HostRuntimeType], records: seq[HostRecord],
    allowDependentSigma = false,
    returnRuntimeValue = false,
    rawGenericValues = false): NimNode =
  ## Emit a sibling wrapper where supported value-indexed generics are
  ## ordinary runtime parameters instead of Nim `static` parameters.
  let generic = genericRuntimeInfo(decl, mappings,
                                   allowUnmappedValue = true)
  if generic.error.len > 0 or generic.genericNames.len == 0 or
      generic.typeNames.len > 0:
    return nil
  let params = decl[3]
  if params.len == 0 or params[0].kind == nnkEmpty: return nil
  # Nim array sizes must be compile-time values. A value-indexed `Dynamic`
  # sibling cannot vary an array's type at runtime, so keep that signature on
  # its ordinary static wrapper and raw Value entry points.
  for mapping in mappings:
    if not mapping.isRuntimeVectorArray: continue
    for genericName in generic.genericNames:
      if mentionsName(params[0], $genericName): return nil
      for i in 1 ..< params.len:
        if mentionsName(params[i][^2], $genericName): return nil
  let resultType = if returnRuntimeValue:
    nil
  else:
    runtimeNimType(params[0], generic.codecMappings, records,
                   allowDependentSigma)
  if not returnRuntimeValue and resultType.isNil: return nil
  var formal = newNimNode(nnkFormalParams)
  formal.add(if returnRuntimeValue:
    parseExpr("tuple[value: Value, globals: Globals]") else: resultType)
  var genericSyms: seq[NimNode] = @[]
  var genericNimTypes: seq[NimNode] = @[]
  for i, genericName in generic.genericNames:
    var dynamicType: NimNode = nil
    if generic.genericNatArgs[i] or generic.genericIntArgs[i]:
      dynamicType = ident"int"
    elif generic.genericBoolArgs[i]:
      dynamicType = ident"bool"
    elif generic.genericValueArgs[i]:
      if not rawGenericValues:
        dynamicType = runtimeNimType(generic.genericValueTypeExprs[i],
          generic.codecMappings, records, allowDependentSigma)
      if dynamicType.isNil: dynamicType = bindSym"Value"
    elif not generic.genericMappedTypes[i].isNil:
      dynamicType = copyNimTree(generic.genericMappedNimTypes[i])
    if dynamicType.isNil: return nil
    let sym = genSym(nskParam, "dynamicGeneric" & $genericName)
    formal.add(newIdentDefs(sym, dynamicType, newEmptyNode()))
    genericSyms.add(sym)
    genericNimTypes.add(dynamicType)
  var argSyms: seq[NimNode] = @[]
  var argNames: seq[string] = @[]
  var argEponymTypes: seq[NimNode] = @[]
  var argNimTypes: seq[NimNode] = @[]
  for i in 1 ..< params.len:
    let p = params[i]
    if p.kind != nnkIdentDefs: return nil
    let argType = runtimeNimType(p[^2], generic.codecMappings, records,
                                 allowDependentSigma)
    if argType.isNil: return nil
    for j in 0 ..< p.len - 2:
      let argName = if p[j].kind == nnkPragmaExpr: p[j][0] else: p[j]
      let argSym = genSym(nskParam, $argName)
      formal.add(newIdentDefs(argSym, argType, newEmptyNode()))
      argSyms.add(argSym)
      argNames.add($argName)
      argEponymTypes.add(p[^2])
      argNimTypes.add(argType)
  let globalsSym = genSym(nskLet, "dynamicGlobals")
  let defsSym = genSym(nskLet, "dynamicDefs")
  let bindingsSym = genSym(nskVar, "dynamicBindings")
  let dirLit = newLit(baseDir)
  let srcLit = newLit(src)
  let nameLit = newLit(defName)
  var body = newStmtList()
  body.add(newLetStmt(globalsSym,
    newCall(bindSym"getGlobalsDir", dirLit, srcLit)))
  var typeIndexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
  for i, genericSym in genericSyms:
    var encodedGeneric: NimNode
    if generic.genericNatArgs[i]:
      encodedGeneric = newCall(bindSym"natToValue", genericSym, globalsSym)
    elif generic.genericBoolArgs[i]:
      encodedGeneric = newCall(bindSym"boolToValue", genericSym, globalsSym)
    elif generic.genericIntArgs[i]:
      encodedGeneric = newCall(bindSym"intToValue", genericSym)
    elif generic.genericValueArgs[i]:
      if genericNimTypes[i].kind == nnkProcTy and not rawGenericValues:
        encodedGeneric = runtimeValueConversionExpr(
          generic.genericValueTypeExprs[i], genericNimTypes[i], genericSym,
          true, generic.codecMappings, records, globalsSym,
          allowDependentSigma)
      else:
        encodedGeneric = copyNimTree(genericSym)
    elif not generic.genericMappedTypes[i].isNil:
      encodedGeneric = runtimeValueConversionExpr(
        generic.genericMappedTypes[i], generic.genericMappedNimTypes[i],
        genericSym, true, generic.codecMappings, records, globalsSym,
        allowDependentSigma)
    if encodedGeneric.isNil: return nil
    var validateEncodedMappedVariant = false
    if not generic.genericValueArgs[i] and
        not generic.genericMappedTypes[i].isNil:
      let mappedHead = runtimeTypeHead(generic.genericValueTypeExprs[i])
      if mappedHead.kind == nnkIdent:
        for mapping in mappings:
          if (mapping.isRuntimeVariant or mapping.isRuntimeStructuredVariant) and
              mapping.eponymName == $mappedHead:
            validateEncodedMappedVariant = true
    if generic.genericValueArgs[i] or validateEncodedMappedVariant:
      let expectedType = runtimeTypeValueExpr(
        generic.genericValueTypeExprs[i], globalsSym, typeIndexOverrides)
      if expectedType.isNil: return nil
      body.add(newCall(bindSym"validateRuntimeValueType",
        encodedGeneric,
        expectedType, globalsSym))
    typeIndexOverrides.add(($generic.genericNames[i], encodedGeneric))
  body.add(newLetStmt(defsSym,
    newCall(bindSym"getDefsDir", dirLit, srcLit)))
  body.add(newVarStmt(bindingsSym, newCall(bindSym"initRuntimeBindings")))
  for binding in bindings:
    body.add(bindingCall(binding, bindingsSym, globalsSym,
                         generic.codecMappings, records))
  var values = newNimNode(nnkBracket)
  var indexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
  for i, genericName in generic.genericNames:
    var encoded: NimNode
    if generic.genericNatArgs[i]:
      encoded = newCall(bindSym"natToValue", genericSyms[i], globalsSym)
    elif generic.genericBoolArgs[i]:
      encoded = newCall(bindSym"boolToValue", genericSyms[i], globalsSym)
    elif generic.genericIntArgs[i]:
      encoded = newCall(bindSym"intToValue", genericSyms[i])
    elif generic.genericValueArgs[i]:
      if genericNimTypes[i].kind == nnkProcTy and not rawGenericValues:
        encoded = runtimeValueConversionExpr(
          generic.genericValueTypeExprs[i], genericNimTypes[i],
          genericSyms[i], true, generic.codecMappings, records, globalsSym,
          allowDependentSigma, indexOverrides)
      else:
        encoded = copyNimTree(genericSyms[i])
    else:
      encoded = runtimeValueConversionExpr(generic.genericMappedTypes[i],
        genericNimTypes[i], genericSyms[i], true, generic.codecMappings,
        records, globalsSym, allowDependentSigma, indexOverrides)
    if encoded.isNil: return nil
    values.add(encoded)
    indexOverrides.add(($genericName, genericSyms[i]))
  for i, argSym in argSyms:
    let encoded = runtimeValueConversionExpr(argEponymTypes[i], argNimTypes[i],
      argSym, true, generic.codecMappings, records, globalsSym,
      allowDependentSigma, indexOverrides)
    if encoded.isNil: return nil
    values.add(encoded)
    indexOverrides.add((argNames[i], argSym))
  let runtimeResult = genSym(nskLet, "dynamicRuntimeResult")
  let call = newCall(bindSym"callDefValueWithBindings",
    newCall(bindSym"findDef", defsSym, nameLit),
    newTree(nnkPrefix, ident"@", values), bindingsSym, globalsSym)
  body.add(newLetStmt(runtimeResult, call))
  if returnRuntimeValue:
    body.add(newTree(nnkTupleConstr, runtimeResult, globalsSym))
  else:
    let decoded = runtimeValueConversionExpr(params[0], resultType,
      runtimeResult, false, generic.codecMappings, records, globalsSym,
      allowDependentSigma, indexOverrides)
    if decoded.isNil: return nil
    body.add(decoded)
  result = newNimNode(nnkProcDef)
  result.add(newTree(nnkPostfix, ident"*", ident(if returnRuntimeValue:
    defName & "RuntimeValueDynamic" else: defName & "Dynamic")))
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(formal)
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  result.add(body)

proc typedRuntimeValueWrapper(decl: NimNode, baseDir, src, defName: string,
                              bindings: seq[HostPostulateBinding],
                              mappings: seq[HostRuntimeType],
                              records: seq[HostRecord],
                              allowDependentSigma = false): NimNode =
  ## Emit a typed host-argument overload that returns the checked result as a
  ## Value. This keeps the definition's full Eponym signature while exposing
  ## only codecs explicitly described by runtimeType and the primitive codecs.
  if decl.kind != nnkProcDef:
    return nil
  let generic = genericRuntimeInfo(decl, mappings)
  if generic.error.len > 0: return nil
  let codecMappings = generic.codecMappings
  let params = decl[3]
  if params.len == 0 or params[0].kind == nnkEmpty:
    return nil

  var formal = newNimNode(nnkFormalParams)
  formal.add(parseExpr("tuple[value: Value, globals: Globals]"))
  var argSyms: seq[NimNode] = @[]
  var argNames: seq[string] = @[]
  var eponymTypes: seq[NimNode] = @[]
  var nimTypes: seq[NimNode] = @[]
  for i in 1 ..< params.len:
    let p = params[i]
    if p.kind != nnkIdentDefs: return nil
    let nimType = runtimeNimType(p[^2], codecMappings, records,
                                 allowDependentSigma)
    if nimType.isNil: return nil
    for j in 0 ..< p.len - 2:
      let argName = if p[j].kind == nnkPragmaExpr: p[j][0] else: p[j]
      let argSym = genSym(nskParam, $argName)
      formal.add(newIdentDefs(argSym, nimType, newEmptyNode()))
      argSyms.add(argSym)
      argNames.add($argName)
      eponymTypes.add(p[^2])
      nimTypes.add(nimType)

  let globalsSym = genSym(nskLet, "runtimeGlobals")
  var values = newNimNode(nnkBracket)
  for genericArg in genericRuntimeValueArgs(generic, globalsSym,
      codecMappings, records):
    values.add(genericArg)
  if hasImportedNullaryUnitArgument(decl):
    values.add(newCall(bindSym"vUnit"))
  var runtimeValueIndexOverrides: seq[tuple[name: string, value: NimNode]] = @[]
  for i, argSym in argSyms:
    let converted = runtimeValueConversionExpr(eponymTypes[i], nimTypes[i],
      argSym, true, codecMappings, records, globalsSym,
      allowDependentSigma, runtimeValueIndexOverrides)
    if converted.isNil: return nil
    values.add(converted)
    runtimeValueIndexOverrides.add((argNames[i], argSym))
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
                           records))
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

proc checkedLambdaArity(definition: ElabDef): int =
  ## Imported definitions have no Nim declaration from which to get arity.
  ## Their checked lambda telescope is the source of truth for the raw ABI.
  var body = definition.tmTm
  while not body.isNil and body.kind == tLam:
    inc result
    body = body.scope.bdy

proc rawRuntimeValueWrapper(baseDir, src, defName: string,
    expectedArity: int,
    bindings: seq[HostPostulateBinding], mappings: seq[HostRuntimeType],
    records: seq[HostRecord], runtimeDecl: NimNode = nil,
    nameSuffix = "RuntimeValue"): NimNode =
  ## Expose a checked definition when no local Nim signature is available.
  ## Callers explicitly pass its arguments as Eponym Values.
  let argsSym = genSym(nskParam, "runtimeArguments")
  let globalsSym = genSym(nskLet, "runtimeGlobals")
  let defsSym = genSym(nskLet, "runtimeDefs")
  let bindingsSym = genSym(nskVar, "runtimeBindings")
  let valueSym = genSym(nskLet, "runtimeValue")
  let dirLit = newLit(baseDir)
  let srcLit = newLit(src)
  let nameLit = newLit(defName)
  let arityLit = newLit(expectedArity)
  var body = newStmtList()
  body.add quote do:
    if `argsSym`.len != `arityLit`:
      raise newException(ValueError,
        "runtimeValue argument count mismatch for " & `nameLit`)
  body.add(newLetStmt(globalsSym,
    newCall(bindSym"getGlobalsDir", dirLit, srcLit)))
  if not runtimeDecl.isNil and runtimeDecl.kind == nnkProcDef and
      runtimeDecl[3].kind == nnkFormalParams:
    var overrides: seq[tuple[name: string, value: NimNode]] = @[]
    var argIndex = 0
    for i in 1 ..< runtimeDecl[3].len:
      let parameter = runtimeDecl[3][i]
      if parameter.kind != nnkIdentDefs: continue
      for parameterOffset in 0 ..< parameter.len - 2:
        let parameterName = if parameter[parameterOffset].kind ==
            nnkPragmaExpr: parameter[parameterOffset][0]
          else: parameter[parameterOffset]
        let rawValue = newTree(nnkBracketExpr, copyNimTree(argsSym),
          newLit(argIndex))
        let check = rawRuntimeValueCheck(parameter[^2], rawValue, globalsSym,
          overrides, mappings, records)
        if not check.isNil: body.add(check)
        overrides.add(($parameterName, rawValue))
        inc argIndex
  body.add(newLetStmt(defsSym,
    newCall(bindSym"getDefsDir", dirLit, srcLit)))
  if runtimeDecl.isNil:
    body.add(newCall(bindSym"validateRuntimeRawArguments",
      newCall(bindSym"findDef", defsSym, nameLit), argsSym, globalsSym,
      runtimeStructuredCodecsExpr(mappings, records)))
  body.add(newVarStmt(bindingsSym, newCall(bindSym"initRuntimeBindings")))
  for binding in bindings:
    body.add(bindingCall(binding, bindingsSym, globalsSym, mappings, records))
  body.add(newLetStmt(valueSym,
    newCall(bindSym"callDefValueWithBindings",
      newCall(bindSym"findDef", defsSym, nameLit), argsSym, bindingsSym,
      globalsSym)))
  body.add(newTree(nnkTupleConstr, valueSym, globalsSym))
  result = newNimNode(nnkProcDef)
  result.add(newTree(nnkPostfix, ident"*", ident(defName & nameSuffix)))
  result.add(newEmptyNode())
  result.add(newEmptyNode())
  var formal = newNimNode(nnkFormalParams)
  formal.add(parseExpr("tuple[value: Value, globals: Globals]"))
  formal.add(newIdentDefs(argsSym,
    newTree(nnkBracketExpr, ident"openArray", bindSym"Value"), newEmptyNode()))
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
  var runtimeDpsNames = initHashSet[string]()
  for st in body:
    if st.kind == nnkCall and st.len == 2 and st[0].kind == nnkIdent and
        $st[0] == "runtimeValue":
      let name = $st[1]
      if name in runtimeValueNames:
        error("duplicate runtimeValue request for '" & name & "'", st)
      runtimeValueNames.incl(name)
    elif st.kind == nnkCall and st.len == 2 and st[0].kind == nnkIdent and
        $st[0] == "runtimeDps":
      let name = $st[1]
      if name in runtimeDpsNames:
        error("duplicate runtimeDps request for '" & name & "'", st)
      runtimeDpsNames.incl(name)
  # Issue #131: imports resolve relative to the calling Nim file's dir.
  let baseDir = callerDir(body)
  var defs: seq[ElabDef]
  var allDefs: seq[ElabDef]
  var checkedGlobals: Globals
  try:
    let checked = elabCheckDirStateAll(src, baseDir)
    defs = checked.defs
    allDefs = checked.allDefs
    checkedGlobals = checked.globals
  except ElabError as e:
    error("eponymBlock elaboration error: " & e.msg, body)
  except ParseError as e:
    error("eponymBlock parse error: " & e.msg, body)

  for requested in runtimeValueNames:
    var found = false
    for d in allDefs:
      if d.name == requested: found = true
    if not found:
      error("runtimeValue names no checked definition: " & requested, body)
    var declaration: NimNode = nil
    for st in body:
      if st.kind == nnkProcDef and $st[0] == requested:
        declaration = st
        break
    if declaration.isNil:
      continue # Imported checked definitions use the raw Value ABI.
    if declaration[3].len == 0 or declaration[3][0].kind == nnkEmpty:
      error("runtimeValue requires a checked definition with a result: " &
        requested, body)
    for i in 1 ..< declaration[3].len:
      if declaration[3][i].kind != nnkIdentDefs:
        error("runtimeValue supports ordinary fixed-arity parameters: " & requested,
          declaration)

  for requested in runtimeDpsNames:
    var checkedDef: ElabDef
    for d in defs:
      if d.name == requested:
        checkedDef = d
        break
    if checkedDef.name.len == 0:
      error("runtimeDps requires a locally declared checked definition: " &
        requested, body)
    var declaration: NimNode = nil
    for st in body:
      if st.kind == nnkProcDef and $st[0] == requested:
        declaration = st
        break
    if declaration.isNil:
      error("runtimeDps requires an explicit Nim proc declaration: " &
        requested, body)
    if declaration[2].kind != nnkEmpty:
      error("runtimeDps does not yet support generic procedures", declaration)
    let params = declaration[3]
    if params.len < 2 or params[0].kind == nnkEmpty or
        $params[0] != "Int":
      error("runtimeDps currently requires an Int result", declaration)
    var valueArity = 0
    for i in 1 ..< params.len:
      let p = params[i]
      if p.kind != nnkIdentDefs or $p[^2] != "Int":
        error("runtimeDps currently requires Int parameters", p)
      valueArity += p.len - 2
    if valueArity == 0:
      error("runtimeDps requires at least one linear Int parameter",
        declaration)
    var term = checkedDef.tmTm
    for i in 0 ..< valueArity:
      if term.isNil or term.kind != tLam:
        error("runtimeDps checked definition has an unexpected lambda shape",
          declaration)
      if term.qty != q1:
        error("runtimeDps requires every parameter to be marked {.linear.}",
          declaration)
      term = term.scope.bdy
    let lowered = tryLowerCheckedLinearInt(term, valueArity)
    if lowered.error.len > 0:
      error("runtimeDps cannot compile '" & requested & "': " &
        lowered.error, declaration)

  var bindings = hostPostulateBindings(body)
  for binding in bindings.mitems:
    if binding.postulateName in checkedGlobals:
      var bindingType = checkedGlobals[binding.postulateName].ty
      while not bindingType.isNil and bindingType.kind == tPi:
        binding.eponymArgumentNames.add(bindingType.scope.adv)
        bindingType = bindingType.scope.bdy
    if binding.pairResult and binding.pairResultType.isNil and
        binding.postulateName in checkedGlobals:
      let checkedShape = runtimeTermTypeAfterArgs(
        checkedGlobals[binding.postulateName].ty, binding.pairArgCount,
        checkedGlobals)
      if not checkedShape.resultType.isNil:
        binding.pairResultType = checkedShape.resultType
        binding.pairResultArgNames = checkedShape.argNames
  for binding in bindings:
    if not bindingIsReferenced(body, binding.postulateName, allDefs,
                               checkedGlobals):
      error("eponymBlock binding error: binding for postulate '" &
        binding.postulateName & "' is unused by every proc body", body)
  let runtimeTypes = hostRuntimeTypes(body, checkedGlobals)
  let trustedRuntimeRecords = trustedRuntimeRecordNames(body)
  let records = hostRecords(body, trustedRuntimeRecords)
  for requested in trustedRuntimeRecords:
    let recordIndex = findHostRecord(records, requested)
    if recordIndex < 0 or records[recordIndex].isVariant:
      error("runtimeRecordTrusted names no record: " & requested, body)
    var hasRuntimeMapping = false
    for mapping in runtimeTypes:
      if mapping.eponymName == requested and not mapping.isRuntimeVector and
          not mapping.isRuntimeList and not mapping.isRuntimeOption and
          not mapping.isRuntimeCodec:
        hasRuntimeMapping = true
    if not hasRuntimeMapping:
      error("runtimeRecordTrusted requires runtimeType(" & requested & ", NimType)",
        body)
  let trustedRuntimePairs = trustedRuntimePairNames(body)
  for requested in trustedRuntimePairs:
    var found = false
    for d in allDefs:
      if d.name == requested: found = true
    if not found:
      error("runtimePairTrusted names no checked definition: " & requested,
        body)
    var declaration: NimNode = nil
    for st in body:
      if st.kind == nnkProcDef and $st[0] == requested:
        declaration = st
        break
    if declaration.isNil:
      var importedDefinition: ElabDef
      for d in allDefs:
        if d.name == requested:
          importedDefinition = d
          break
      if importedDefinition.name.len > 0:
        declaration = importedRuntimeProcDecl(importedDefinition,
          checkedGlobals)
    if declaration.isNil:
      error("runtimePairTrusted requires a local Nim declaration or a " &
        "reconstructable imported signature for: " & requested, body)
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
      if mapping.isRuntimeVector:
        validateHostVectorCodec(checkedGlobals, mapping.eponymName)
      elif mapping.isRuntimeList:
        validateHostListCodec(checkedGlobals, mapping.eponymName)
      elif mapping.isRuntimeOption:
        validateHostOptionCodec(checkedGlobals, mapping.eponymName)
      elif mapping.isRuntimeVariant or mapping.isRuntimeStructuredVariant:
        let constructors = runtimeVariantConstructorNames(checkedGlobals,
          mapping.eponymName)
        validateRuntimeVariantConstructors(checkedGlobals,
          mapping.eponymName, constructors)
      elif mapping.isRuntimeCodec:
        validateHostRuntimeCodecType(checkedGlobals, mapping.eponymName)
      else:
        let recordIndex = findHostRecord(records, mapping.eponymName)
        if recordIndex >= 0:
          let record = records[recordIndex]
          if record.isVariant and
              (record.hasDependentField or record.constructors.len == 0):
            raise newException(ValueError,
              "runtime enum codec for '" & mapping.eponymName &
              "' requires only nullary constructors returning the unindexed family")
        else:
          validateHostOpaqueType(checkedGlobals, mapping.eponymName)
    except ValueError as e:
      error("eponymBlock runtimeType error: " & e.msg, body)
  for binding in bindings:
    try:
      validateLocalBindingTypeExpressions(body, binding)
      validateAppliedBindingTypeExpressions(checkedGlobals, binding)
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
      var usesCustomCodec = false
      for typeName in binding.eponymTypes:
        for mapping in runtimeTypes:
          if mapping.eponymName == typeName and mapping.isRuntimeCodec:
            usesCustomCodec = true
      for typeExpr in binding.eponymTypeExprs:
        if typeExpr.kind != nnkIdent: usesCustomCodec = true
      if binding.eponymTypes.len >= 7 or usesCustomCodec:
        var adapterTypes = binding.eponymTypes
        if binding.eponymTypes.len == 1:
          adapterTypes = @[binding.eponymTypes[0], binding.eponymTypes[0]]
        if binding.eponymTypeExprs.len > 0:
          var typeHeads: seq[string] = @[]
          var hasNonNamedType = false
          for typeExpr in binding.eponymTypeExprs:
            let head = runtimeTypeHead(typeExpr)
            if head.isNil or head.kind != nnkIdent:
              hasNonNamedType = true
              break
            typeHeads.add($head)
          if not hasNonNamedType:
            if typeHeads.len == 1: typeHeads = @[typeHeads[0], typeHeads[0]]
            validateHostMappedNaryType(checkedGlobals, binding.postulateName,
                                       typeHeads)
        else:
          validateHostMappedNaryType(checkedGlobals, binding.postulateName,
                                     adapterTypes)
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
        if binding.eponymTypes[1] == "Nat":
          validateHostOpaqueNatUnaryType(checkedGlobals,
            binding.postulateName, binding.eponymTypes[0])
        else:
          validateHostOpaqueMapUnaryType(checkedGlobals,
            binding.postulateName, binding.eponymTypes[0],
            binding.eponymTypes[1])
      of 3:
        if binding.eponymTypes[0] == "Nat":
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
    if procDecl.isNil:
      procDecl = importedRuntimeProcDecl(d, checkedGlobals)
    if not procDecl.isNil:
      if d.name in runtimeValueNames:
        let params = procDecl[3]
        let generic = genericRuntimeInfo(procDecl, runtimeTypes)
        var valueArity = 0
        for i in 1 ..< params.len:
          valueArity += params[i].len - 2
        let runtimeName = ident(d.name & "RuntimeValue")
        if procDecl[2].kind != nnkEmpty:
          let genericArgsSym = genSym(nskParam, "runtimeGenericArguments")
          let valueArgsSym = genSym(nskParam, "runtimeValueArguments")
          let globalsSym = genSym(nskLet, "runtimeGlobals")
          let defsSym = genSym(nskLet, "runtimeDefs")
          let bindingsSym = genSym(nskVar, "runtimeBindings")
          let nameLit = newLit(d.name)
          let dirLit = newLit(baseDir)
          let srcLit = newLit(src)
          let genericArity = newLit(block:
            var arity = 0
            for param in procDecl[2]:
              arity += param.len - 2
            arity)
          let valueArity = newLit(block:
            var arity = 0
            for i in 1 ..< params.len:
              arity += params[i].len - 2
            arity)
          var rawBody = newStmtList()
          rawBody.add quote do:
            if `genericArgsSym`.len != `genericArity`:
              raise newException(ValueError,
                "runtimeValue generic argument count mismatch for " & `nameLit`)
            if `valueArgsSym`.len != `valueArity`:
              raise newException(ValueError,
                "runtimeValue argument count mismatch for " & `nameLit`)
          rawBody.add(newLetStmt(globalsSym,
            newCall(bindSym"getGlobalsDir", dirLit, srcLit)))
          var genericTypeOverrides: seq[tuple[name: string,
            value: NimNode]] = @[]
          var rawRuntimeMappings = runtimeTypes
          for typeName in generic.typeNames:
            rawRuntimeMappings.add(HostRuntimeType(eponymName: typeName,
              nimType: ident(typeName), isSynthetic: true))
          var genericArgIndex = 0
          for genericParam in procDecl[2]:
            for binderOffset in 0 ..< genericParam.len - 2:
              let binderName = if genericParam[binderOffset].kind ==
                  nnkPragmaExpr: genericParam[binderOffset][0]
                else: genericParam[binderOffset]
              let binderType = genericParam[^2]
              if nimTypeToEponym(binderType) != "Type 0":
                let expectedType = runtimeTypeValueExpr(binderType,
                  globalsSym, genericTypeOverrides)
                if not expectedType.isNil:
                  let genericValue = newTree(nnkBracketExpr,
                    copyNimTree(genericArgsSym), newLit(genericArgIndex))
                  rawBody.add(newCall(bindSym"validateRuntimeValueType",
                    genericValue, expectedType, copyNimTree(globalsSym)))
              let genericValue = newTree(nnkBracketExpr,
                copyNimTree(genericArgsSym), newLit(genericArgIndex))
              genericTypeOverrides.add(($binderName, genericValue))
              inc genericArgIndex
          var rawValueIndex = 0
          for i in 1 ..< params.len:
            let parameter = params[i]
            for parameterOffset in 0 ..< parameter.len - 2:
              let parameterName = if parameter[parameterOffset].kind ==
                  nnkPragmaExpr: parameter[parameterOffset][0]
                else: parameter[parameterOffset]
              let rawValue = newTree(nnkBracketExpr,
                copyNimTree(valueArgsSym), newLit(rawValueIndex))
              let check = rawRuntimeValueCheck(parameter[^2], rawValue,
                globalsSym, genericTypeOverrides, rawRuntimeMappings, records)
              if not check.isNil: rawBody.add(check)
              genericTypeOverrides.add(($parameterName, rawValue))
              inc rawValueIndex
          rawBody.add(newLetStmt(defsSym,
            newCall(bindSym"getDefsDir", dirLit, srcLit)))
          rawBody.add(newVarStmt(bindingsSym,
            newCall(bindSym"initRuntimeBindings")))
          for binding in bindings:
            rawBody.add(bindingCall(binding, bindingsSym, globalsSym,
                                    runtimeTypes, records))
          let allArgsSeq = genSym(nskLet, "allRuntimeArguments")
          rawBody.add(newLetStmt(allArgsSeq, newCall(bindSym"concat",
            newCall(bindSym"toSeq", genericArgsSym),
            newCall(bindSym"toSeq", valueArgsSym))))
          rawBody.add(newTree(nnkTupleConstr,
            newCall(bindSym"callDefValueWithBindings",
              newCall(bindSym"findDef", defsSym, nameLit), allArgsSeq,
              bindingsSym, globalsSym), globalsSym))
          var rawProc = newNimNode(nnkProcDef)
          rawProc.add(newTree(nnkPostfix, ident"*",
                              ident(d.name & "RuntimeValueRaw")))
          rawProc.add(newEmptyNode())
          rawProc.add(newEmptyNode())
          var rawFormal = newNimNode(nnkFormalParams)
          rawFormal.add(parseExpr("tuple[value: Value, globals: Globals]"))
          rawFormal.add(newIdentDefs(genericArgsSym,
            newTree(nnkBracketExpr, ident"openArray", bindSym"Value"),
            newEmptyNode()))
          rawFormal.add(newIdentDefs(valueArgsSym,
            newTree(nnkBracketExpr, ident"openArray", bindSym"Value"),
            newEmptyNode()))
          rawProc.add(rawFormal)
          rawProc.add(newEmptyNode())
          rawProc.add(newEmptyNode())
          rawProc.add(rawBody)
          result.add(rawProc)
        let globalsSym = genSym(nskLet, "runtimeGlobals")
        let defsSym = genSym(nskLet, "runtimeDefs")
        let bindingsSym = genSym(nskVar, "runtimeBindings")
        let argsSym = genSym(nskParam, "runtimeArguments")
        var genericValues = newNimNode(nnkBracket)
        if generic.error.len == 0:
          for genericArg in genericRuntimeValueArgs(generic, globalsSym,
              runtimeTypes, records):
            genericValues.add(copyNimTree(genericArg))
        if hasImportedNullaryUnitArgument(procDecl):
          genericValues.add(newCall(bindSym"vUnit"))
        let runtimeArgsSym = newCall(bindSym"prependRuntimeArgs",
          newTree(nnkPrefix, ident"@", genericValues), argsSym)
        let expectedArity = newLit(valueArity)
        var bindingStatements = newStmtList()
        for binding in bindings:
          bindingStatements.add(bindingCall(binding, bindingsSym, globalsSym,
                                            runtimeTypes, records))
        var rawBody = newStmtList()
        rawBody.add quote do:
          if `argsSym`.len != `expectedArity`:
            raise newException(ValueError,
              "runtimeValue argument count mismatch for " & `nameLit`)
        rawBody.add quote do:
            let `globalsSym` = getGlobalsDir(`dirLit`, `srcLit`)
            let `defsSym` = getDefsDir(`dirLit`, `srcLit`)
            var `bindingsSym` = initRuntimeBindings()
        var rawArgumentOverrides: seq[tuple[name: string,
          value: NimNode]] = @[]
        var rawRuntimeMappings = runtimeTypes
        for typeName in generic.typeNames:
          rawRuntimeMappings.add(HostRuntimeType(eponymName: typeName,
            nimType: ident(typeName), isSynthetic: true))
        if generic.error.len == 0:
          for i, genericName in generic.genericNames:
            rawArgumentOverrides.add(($genericName,
              copyNimTree(genericValues[i])))
          var rawArgumentIndex = 0
          for i in 1 ..< params.len:
            let parameter = params[i]
            for parameterOffset in 0 ..< parameter.len - 2:
              let parameterName = if parameter[parameterOffset].kind ==
                  nnkPragmaExpr: parameter[parameterOffset][0]
                else: parameter[parameterOffset]
              let rawValue = newTree(nnkBracketExpr,
                copyNimTree(argsSym), newLit(rawArgumentIndex))
              let check = rawRuntimeValueCheck(parameter[^2], rawValue,
                globalsSym, rawArgumentOverrides, rawRuntimeMappings, records)
              if not check.isNil: rawBody.add(check)
              rawArgumentOverrides.add(($parameterName, rawValue))
              inc rawArgumentIndex
        rawBody.add(bindingStatements)
        rawBody.add quote do:
            (callDefValueWithBindings(findDef(`defsSym`, `nameLit`), `runtimeArgsSym`,
                                      `bindingsSym`), `globalsSym`)
        if generic.error.len == 0:
          var rawProc = newNimNode(nnkProcDef)
          rawProc.add(newTree(nnkPostfix, ident("*"), runtimeName))
          rawProc.add(newEmptyNode())
          rawProc.add(copyNimTree(generic.genericParams))
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
        if valueArity == 0 and generic.error.len == 0:
          var forwarderBody = newStmtList()
          var rawCallee: NimNode = copyNimTree(runtimeName)
          if generic.genericNames.len > 0:
            var genericCallArgs = newNimNode(nnkBracket)
            for genericName in generic.genericNames:
              genericCallArgs.add(copyNimTree(genericName))
            rawCallee = newTree(nnkBracketExpr, rawCallee, genericCallArgs)
          forwarderBody.add(newCall(rawCallee, newNimNode(nnkBracket)))
          var forwarder = newNimNode(nnkProcDef)
          forwarder.add(newTree(nnkPostfix, ident("*"),
                                ident(d.name & "RuntimeValue")))
          forwarder.add(newEmptyNode())
          forwarder.add(copyNimTree(generic.genericParams))
          var forwarderFormal = newNimNode(nnkFormalParams)
          forwarderFormal.add(parseExpr("tuple[value: Value, globals: Globals]"))
          forwarder.add(forwarderFormal)
          forwarder.add(newEmptyNode())
          forwarder.add(newEmptyNode())
          forwarder.add(forwarderBody)
          result.add(forwarder)
        else:
          let allowDependentSigma = d.name in trustedRuntimePairs
          let typedValueWrapper = typedRuntimeValueWrapper(procDecl,
            baseDir, src, d.name, bindings, runtimeTypes, records,
            allowDependentSigma)
          if not typedValueWrapper.isNil:
            result.add(typedValueWrapper)
      let allowDependentSigma = d.name in trustedRuntimePairs
      let typedWrapper = typedRuntimeWrapper(procDecl, baseDir, src, d.name,
        bindings, runtimeTypes, records, allowDependentSigma)
      if not typedWrapper.isNil:
        result.add(typedWrapper)
      else:
        result.add(unsupportedRuntimeWrapper(procDecl, d.name, runtimeTypes,
          records, allowDependentSigma))
      let dynamicWrapper = dynamicGenericRuntimeWrapper(procDecl, baseDir,
        src, d.name, bindings, runtimeTypes, records, allowDependentSigma)
      if not dynamicWrapper.isNil:
        result.add(dynamicWrapper)
      if hasTypedGenericCallback(procDecl, runtimeTypes, records,
                                 allowDependentSigma):
        let rawDynamicWrapper = dynamicGenericRuntimeWrapper(procDecl,
          baseDir, src, d.name, bindings, runtimeTypes, records,
          allowDependentSigma, rawGenericValues = true)
        if not rawDynamicWrapper.isNil: result.add(rawDynamicWrapper)
      if d.name in runtimeValueNames:
        let dynamicRuntimeValueWrapper = dynamicGenericRuntimeWrapper(procDecl,
          baseDir, src, d.name, bindings, runtimeTypes, records,
          allowDependentSigma, returnRuntimeValue = true)
        if not dynamicRuntimeValueWrapper.isNil:
          result.add(dynamicRuntimeValueWrapper)
        if hasTypedGenericCallback(procDecl, runtimeTypes, records,
                                   allowDependentSigma):
          let rawDynamicRuntimeValueWrapper = dynamicGenericRuntimeWrapper(
            procDecl, baseDir, src, d.name, bindings, runtimeTypes, records,
            allowDependentSigma, returnRuntimeValue = true,
            rawGenericValues = true)
          if not rawDynamicRuntimeValueWrapper.isNil:
            result.add(rawDynamicRuntimeValueWrapper)
      if d.name in runtimeDpsNames:
        var parameterNames: seq[string] = @[]
        for i in 1 ..< procDecl[3].len:
          let p = procDecl[3][i]
          for j in 0 ..< p.len - 2:
            let nameNode = if p[j].kind == nnkPragmaExpr: p[j][0] else: p[j]
            parameterNames.add($nameNode)
        var term = d.tmTm
        for _ in 0 ..< parameterNames.len:
          term = term.scope.bdy
        let lowered = tryLowerCheckedLinearInt(term, parameterNames.len)
        if lowered.error.len > 0:
          error("runtimeDps cannot compile '" & d.name & "': " &
            lowered.error, procDecl)
        result.add(generateLinearIntDpsProc(d.name & "Dps", parameterNames,
                                             lowered.expression))
      continue
    if d.name in runtimeValueNames:
      result.add(rawRuntimeValueWrapper(baseDir, src, d.name,
        checkedLambdaArity(d), bindings, runtimeTypes, records))
    let name = ident(d.name)
    let message = newLit("eponymBlock wrapper '" & d.name &
      "': no Nim signature could be reconstructed for this definition; " &
      "declare a typed proc signature or expose it with runtimeValue and " &
      "use the raw Value interface")
    result.add(quote do:
      template `name`*(args: varargs[untyped]): untyped =
        {.error: `message`.}
    )
  for requested in runtimeValueNames:
    var localDef = false
    for d in defs:
      if d.name == requested:
        localDef = true
        break
    if not localDef:
      var importedDef: ElabDef
      for d in allDefs:
        if d.name == requested:
          importedDef = d
          break
      if importedDef.name.len > 0:
        let importedDecl = importedRuntimeProcDecl(importedDef,
          checkedGlobals)
        if not importedDecl.isNil:
          let allowDependentSigma = requested in trustedRuntimePairs
          let typedImportedWrapper = typedRuntimeWrapper(importedDecl,
            baseDir, src, requested, bindings, runtimeTypes, records,
            allowDependentSigma)
          if not typedImportedWrapper.isNil:
            result.add(typedImportedWrapper)
          else:
            result.add(unsupportedRuntimeWrapper(importedDecl, requested,
              runtimeTypes, records, allowDependentSigma))
          let typedImportedValueWrapper = typedRuntimeValueWrapper(
            importedDecl, baseDir, src, requested, bindings, runtimeTypes,
            records, allowDependentSigma)
          if not typedImportedValueWrapper.isNil:
            result.add(typedImportedValueWrapper)
          let importedDynamicWrapper = dynamicGenericRuntimeWrapper(
            importedDecl, baseDir, src, requested, bindings, runtimeTypes,
            records, allowDependentSigma)
          if not importedDynamicWrapper.isNil:
            result.add(importedDynamicWrapper)
          if hasTypedGenericCallback(importedDecl, runtimeTypes, records,
                                     allowDependentSigma):
            let importedRawDynamicWrapper = dynamicGenericRuntimeWrapper(
              importedDecl, baseDir, src, requested, bindings, runtimeTypes,
              records, allowDependentSigma, rawGenericValues = true)
            if not importedRawDynamicWrapper.isNil:
              result.add(importedRawDynamicWrapper)
          let importedDynamicRuntimeValueWrapper =
            dynamicGenericRuntimeWrapper(importedDecl, baseDir, src,
              requested, bindings, runtimeTypes, records, allowDependentSigma,
              returnRuntimeValue = true)
          if not importedDynamicRuntimeValueWrapper.isNil:
            result.add(importedDynamicRuntimeValueWrapper)
          if hasTypedGenericCallback(importedDecl, runtimeTypes, records,
                                     allowDependentSigma):
            let importedRawDynamicRuntimeValueWrapper =
              dynamicGenericRuntimeWrapper(importedDecl, baseDir, src,
                requested, bindings, runtimeTypes, records,
                allowDependentSigma, returnRuntimeValue = true,
                rawGenericValues = true)
            if not importedRawDynamicRuntimeValueWrapper.isNil:
              result.add(importedRawDynamicRuntimeValueWrapper)
        var rawImportedDecl = importedDecl
        var rawRuntimeValueSuffix = "RuntimeValue"
        if not rawImportedDecl.isNil and
            rawImportedDecl[2].kind == nnkGenericParams and
            rawImportedDecl[2].len > 0:
          rawImportedDecl = nil
          rawRuntimeValueSuffix = "RuntimeValueRaw"
        result.add(rawRuntimeValueWrapper(baseDir, src, requested,
          checkedLambdaArity(importedDef), bindings, runtimeTypes, records,
          rawImportedDecl, rawRuntimeValueSuffix))

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
