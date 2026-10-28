## Issue #478: one block type — eponymBlock with use-gated sheds.
##
## Macro-level tests: the old shedsBlock is gone, so these exercise the
## unified block directly by shelling out to `nim c`, the way the
## extension does (same harness shape as test_shed_sidecar_reset.nim).
## Positive fixtures must compile AND run; negative fixtures must fail
## compilation with the gating error naming the shed.
##
## Run: nim c -r --hints:off --path:src --path:src/eponym tests/test_unified_block.nim
import os
import osproc
import strutils
import json

const RepoRoot = parentDir(parentDir(currentSourcePath()))

proc nimCmd(): string =
  let n = findExe("nim")
  doAssert n.len > 0, "nim not on PATH"
  n

proc compileSrc(src: string, run: bool): tuple[ok: bool, output: string] =
  let flag = if run: "c -r" else: "c"
  let cmd = nimCmd() & " " & flag & " --hints:off --path:\"" & RepoRoot / "src" &
    "\" --path:\"" & RepoRoot / "src" / "eponym" &
    "\" -o:\"" & src.changeFileExt("") & "\" \"" & src & "\""
  let (outp, code) = execCmdEx(cmd)
  (code == 0, outp)

proc writeSrc(dir, name, body: string): string =
  result = dir / name
  writeFile(result, "import eponym_mac\n\n" & body)

var failures = 0
proc check(cond: bool, label: string) =
  if cond: echo "ok: ", label
  else:
    inc failures
    echo "FAIL: ", label

proc sidecarStatuses(nimFile: string): seq[tuple[name, status: string]] =
  let (dir, base, _) = splitFile(nimFile)
  let j = parseJson(readFile(dir / (base & ".sheds.json")))
  for s in j["sheds"].elems:
    result.add((s["name"].getStr, s["status"].getStr))

when isMainModule:
  let dir = getTempDir() / "unified_block"
  removeDir(dir)
  createDir(dir)

  # --- Positive: filled shed is an ordinary compiled def ---------------
  let filled = writeSrc(dir, "filled.nim", """eponymBlock:
  postulate(Int, Univ)
  proc double(x: Int): Int = addInt(x, x)
  proc quad(n: Int): Int = ![quadBody, double (double n)]
echo quad(3)
echo double(21)
""")
  let (okFilled, outFilled) = compileSrc(filled, true)
  check(okFilled, "filled shed: compiles and runs, got: " & outFilled)
  check("12" in outFilled.splitLines() and "42" in outFilled.splitLines(),
    "filled shed: quad(3) = 12 and double(21) = 42")

  # --- Positive: open shed unused, complete defs callable; sidecar ----
  let openUnused = writeSrc(dir, "open_unused.nim", """eponymBlock:
  postulate(Int, Univ)
  proc double(x: Int): Int = addInt(x, x)
  proc quad(n: Int): Int = ![quadBody, n ++++ n]
  proc quadOpen(n: Int): Int = ![quadOpenBody]
echo double(21)
""")
  let (okOpen, outOpen) = compileSrc(openUnused, true)
  check(okOpen, "open shed unused: compiles and runs, got: " & outOpen)
  check("42" in outOpen.splitLines(), "open shed unused: double(21) = 42")
  let st = sidecarStatuses(openUnused)
  check(st.len == 2 and st[0].status == "yellow" and st[1].status == "yellow",
    "open shed unused: both sheds yellow, got: " & $st)

  # --- Positive: filled + open sidecar statuses ------------------------
  let mixed = writeSrc(dir, "mixed.nim", """eponymBlock:
  postulate(Int, Univ)
  proc double(x: Int): Int = addInt(x, x)
  proc quad(n: Int): Int = ![quadBody, double (double n)]
  proc quadOpen(n: Int): Int = ![quadOpenBody]
echo double(21)
""")
  let (okMixed, _) = compileSrc(mixed, true)
  check(okMixed, "mixed: compiles and runs")
  let stMixed = sidecarStatuses(mixed)
  check(stMixed.len == 2 and stMixed[0].status == "white" and
        stMixed[1].status == "yellow",
    "mixed: filled shed white, open shed yellow, got: " & $stMixed)

  # --- Positive: plain hole unused (not just sheds) is use-gated too ---
  let plainHole = writeSrc(dir, "plain_hole.nim", """eponymBlock:
  postulate(Int, Univ)
  proc double(x: Int): Int = addInt(x, x)
  proc mystery(n: Int): Int = _
echo double(21)
""")
  let (okPlain, _) = compileSrc(plainHole, true)
  check(okPlain, "plain hole unused: compiles and runs")

  # --- Positive: type-position shed, filled, is callable ---------------
  let tyFilled = writeSrc(dir, "ty_filled.nim", """eponymBlock:
  postulate(Int, Univ)
  proc f(n: Int): ![tyBody, Int] = n
echo f(7)
""")
  let (okTy, outTy) = compileSrc(tyFilled, true)
  check(okTy, "type-position shed filled: compiles and runs, got: " & outTy)
  check("7" in outTy.splitLines(), "type-position shed filled: f(7) = 7")

  # --- Positive (issue #479): generic callee through a compiled caller -
  let generic = writeSrc(dir, "generic.nim", """eponymBlock:
  postulate(Int, Univ)
  proc checkedIdentity[A: Univ](value: A): A = value
  proc useGeneric(v: Int): Int = checkedIdentity[Int](v)
echo useGeneric(17)
""")
  let (okGen, outGen) = compileSrc(generic, true)
  check(okGen, "generic callee: compiles and runs, got: " & outGen)
  check("17" in outGen.splitLines(), "generic callee: useGeneric(17) = 17")

  # --- Negative: calling an open-shed def is a compile error ----------
  let callOpen = writeSrc(dir, "call_open.nim", """eponymBlock:
  postulate(Int, Univ)
  proc quad(n: Int): Int = ![quadBody, n ++++ n]
echo quad(3)
""")
  let (okCallOpen, outCallOpen) = compileSrc(callOpen, false)
  check(not okCallOpen, "calling open shed: compilation fails")
  check("quadBody" in outCallOpen and "incomplete" in outCallOpen,
    "calling open shed: error names the shed, got: " & outCallOpen)

  # --- Negative: transitive gating through a compiled caller -----------
  let transit = writeSrc(dir, "transit.nim", """eponymBlock:
  postulate(Int, Univ)
  proc quad(n: Int): Int = ![quadBody]
  proc useQuad(n: Int): Int = quad(n)
echo useQuad(3)
""")
  let (okTransit, outTransit) = compileSrc(transit, false)
  check(not okTransit, "transitive caller: compilation fails")
  check("calls gated" in outTransit and "quad" in outTransit,
    "transitive caller: error names the gated callee, got: " & outTransit)

  # --- Negative: bad draft, used ---------------------------------------
  let badDraft = writeSrc(dir, "bad_draft_use.nim", """eponymBlock:
  postulate(Int, Univ)
  proc quad(n: Int): Int = ![quadBody, n ++++ n]
echo quad(3)
""")
  let (okBad, outBad) = compileSrc(badDraft, false)
  check(not okBad, "bad draft used: compilation fails")
  check("draft failed" in outBad,
    "bad draft used: error reports the draft failure, got: " & outBad)

  # --- Negative: requireCompiled + open shed is a hard macro error -----
  let reqComp = writeSrc(dir, "reqcomp.nim", """eponymBlock:
  requireCompiled()
  postulate(Int, Univ)
  proc quad(n: Int): Int = ![quadBody]
""")
  let (okReq, outReq) = compileSrc(reqComp, false)
  check(not okReq, "requireCompiled + open shed: compilation fails")
  check("requireCompiled" in outReq and "incomplete" in outReq,
    "requireCompiled + open shed: error names the guarantee, got: " & outReq)

  if failures > 0:
    echo "FAILURES: ", failures
    quit(1)
  echo "--- unified block contract passed ---"
