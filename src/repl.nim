## Issue #50: interactive read-eval loop for Eponym.
##
## Build:  nim c --path:src --path:src/eponym src/repl.nim
## Run:    ./repl            (then type at the prompt)
##
## A ModuleDriver holds the persistent elaboration environment (globals,
## metavariables, name supply), so declarations accumulate across inputs.
## Each input line is either a REPL command (`:type`, `:eval`, `:load`,
## `:help`, `:quit`) or surface source, which is parsed and elaborated into
## the driver. Multi-line declarations are supported: lines accumulate until
## the buffer parses as a program; a blank line forces an elaboration attempt
## so genuine syntax errors surface instead of waiting for more input.
## Elaboration and parse errors print as located messages and the session
## continues. `:eval` evaluates to weak-head normal form and prints it with
## a small value printer (no Term readback needed).

import os
import strutils
import tables
import elab
import parse_surf
import eponym_init
import unify  # zonk

const prompt = "eponym> "
const contPrompt = "......> "

proc prettyWhnfVal(v: Value, lvl: int, varNames: var seq[string],
                   refNames: Table[int, string]): string =
  ## Print a weak-head normal value. Binders are printed under a fresh
  ## neutral variable (de Bruijn level `lvl`, tracked in `varNames`);
  ## neutral heads resolve through `refNames` (negative ids are the
  ## fresh binder variables).
  case whnfKind(v)
  of wConst: $whnfConst(v)
  of wInt: $whnfIntVal(v)
  of wNatLit: $whnfNatLitVal(v)
  of wNatSing: $whnfNatSingVal(v)  # Issue #74: singleton type prints as the literal
  of wRef:
    let id = whnfRefId(v)
    var s =
      if id < 0: varNames[-(id + 1)]
      elif id in refNames: refNames[id]
      else: "R" & $id
    for i in 0 ..< whnfSpineLen(v):
      let a = prettyWhnfVal(whnfSpineArg(v, i), lvl, varNames, refNames)
      case whnfSpineKind(v, i)
      of eApp: s = "(" & s & " " & a & ")"
      of eFst: s = "(" & s & ".1)"
      of eSnd: s = "(" & s & ".2)"
      of eAbsurd: s = "(absurd " & s & ")"
    s
  of wPi, wSi, wLam, wLam0:
    var adv = whnfScopeAdv(v)
    if adv == "" or adv == "_": adv = "x" & $lvl
    var nm = adv
    var k = 0
    while nm in varNames: inc k; nm = adv & $k
    varNames.add(nm)
    let fresh = neutralVar(lvl)
    let body = prettyWhnfVal(whnfScopeApply(v, fresh), lvl + 1, varNames,
                             refNames)
    discard varNames.pop()
    let kw =
      case whnfKind(v)
      of wPi: "Pi "
      of wSi: "Si "
      else: ""
    if whnfKind(v) == wLam or whnfKind(v) == wLam0:
      let qtyPrefix = if whnfKind(v) == wLam0: "(0 " else: ""
      "lam " & qtyPrefix & nm & (if qtyPrefix.len > 0: ")" else: "") &
        ". " & body
    else:
      let dom = "(" & nm & " : " &
        prettyWhnfVal(whnfDom(v), lvl, varNames, refNames) & ") "
      kw & dom & ". " & body
  of wPair:
    "(" & prettyWhnfVal(whnfFst(v), lvl, varNames, refNames) & ", " &
      prettyWhnfVal(whnfSnd(v), lvl, varNames, refNames) & ")"
  of wPrim:
    var s = "prim " & $whnfPrimOp(v)
    for a in whnfPrimArgs(v):
      s &= " " & prettyWhnfVal(a, lvl, varNames, refNames)
    "(" & s & ")"
  of wRed:
    let id = whnfRedId(v)
    var s = if id in refNames: refNames[id] else: "elim" & $id
    for a in whnfRedArgs(v):
      s &= " " & prettyWhnfVal(a, lvl, varNames, refNames)
    "(" & s & ")"
  of wType:
    # Issue #52: level-annotated universe value.
    "Type " & $univIdx(v)
  of wHost:
    "<host " & whnfHostTypeName(v) & ">"

proc prettyWhnf*(v: Value, refNames: Table[int, string]): string =
  ## Issue #50: user-facing WHNF printer (entry point for `:eval`).
  var varNames: seq[string] = @[]
  prettyWhnfVal(v, 0, varNames, refNames)

type Session = object
  drv: ModuleDriver
  buf: string  ## accumulated multi-line source input

proc printDefs(s: Session, defs: seq[ElabDef]) =
  for d in defs:
    echo d.name, " : ",
      prettyTerm(zonk(s.drv.ms, d.tyTm), @[], s.drv.ms.refNames,
                 s.drv.ms.recordFields)

proc elabSource(s: var Session, src: string) =
  ## Parse and elaborate surface source into the session's driver.
  let decls =
    try: parseProgram(src)
    except ParseError as e:
      echo "parse error: ", e.msg
      return
  let defs =
    try: s.drv.elabDeclsDir(decls, getCurrentDir(), "<repl>")
    except ElabError as e:
      echo "error: ", e.msg
      return
  s.printDefs(defs)

proc cmdType(s: var Session, arg: string) =
  let pre =
    try: parseTermStr(arg)
    except ParseError as e:
      echo "parse error: ", e.msg
      return
  try:
    let (_, ty) = inferTm(pre, @[], s.drv.globals, s.drv.ms, s.drv.supply, nil)
    echo prettyTerm(zonk(s.drv.ms, ty), @[], s.drv.ms.refNames,
                    s.drv.ms.recordFields)
  except ElabError as e:
    echo "error: ", e.msg

proc cmdEval(s: var Session, arg: string) =
  let pre =
    try: parseTermStr(arg)
    except ParseError as e:
      echo "parse error: ", e.msg
      return
  try:
    let (tm, _) = inferTm(pre, @[], s.drv.globals, s.drv.ms, s.drv.supply, nil)
    let v = eval(zonk(s.drv.ms, tm), @[])
    echo prettyWhnf(v, s.drv.ms.refNames)
  except ElabError as e:
    echo "error: ", e.msg
  except ValueError as e:
    # e.g. evaluating an open metavariable (should not happen post-zonk)
    echo "error: ", e.msg

proc cmdLoad(s: var Session, arg: string) =
  let path = arg.strip()
  if path.len == 0:
    echo "usage: :load <file.ep>"
    return
  try:
    let defs = s.drv.elabFile(path)
    if defs.len == 0:
      echo "(no new definitions)"
    else:
      s.printDefs(defs)
  except ElabError as e:
    echo "error: ", e.msg

proc printHelp() =
  echo """commands:
  :type <tm>   infer and print the type of <tm>
  :eval <tm>   evaluate <tm> to weak-head normal form and print it
  :load <file> elaborate a .ep file into the session (imports resolve
              relative to the file's directory)
  :help        this message
  :quit        exit
anything else is Eponym source: declarations elaborate into the session and
stay in scope. Multi-line declarations are fine; a blank line forces the
pending input to elaborate (so syntax errors are reported)."""

proc runCommand(s: var Session, line: string): bool =
  ## Returns false when the session should quit.
  let words = line.splitWhitespace(maxsplit = 1)
  let cmd = words[0]
  let arg = if words.len > 1: words[1] else: ""
  case cmd
  of ":quit", ":q": return false
  of ":type", ":t": s.cmdType(arg)
  of ":eval", ":e": s.cmdEval(arg)
  of ":load", ":l": s.cmdLoad(arg)
  of ":help", ":h", ":?": printHelp()
  else: echo "unknown command: ", cmd, " (try :help)"
  true

proc repl() =
  var s = Session(drv: initModuleDriver())
  echo "Eponym REPL — :help for commands, :quit to exit."
  var running = true
  while running:
    stdout.write(if s.buf.len == 0: prompt else: contPrompt)
    stdout.flushFile()
    var line: string
    try:
      line = stdin.readLine()
    except EOFError:
      break
    if line.strip().startsWith(":"):
      # A command always takes effect; flush pending source input first.
      if s.buf.len > 0:
        s.elabSource(s.buf)
        s.buf = ""
      running = s.runCommand(line.strip())
      continue
    if line.strip().len == 0:
      # A blank line forces the pending buffer to elaborate, surfacing
      # syntax errors instead of waiting for more input.
      if s.buf.len > 0:
        s.elabSource(s.buf)
        s.buf = ""
      continue
    s.buf &= line & "\n"
    # Elaborate eagerly once the buffer is a complete program.
    var complete = false
    try:
      discard parseProgram(s.buf)
      complete = true
    except ParseError:
      discard
    if complete:
      s.elabSource(s.buf)
      s.buf = ""

when isMainModule:
  repl()
