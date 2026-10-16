## Regression test: VM-safe per-compilation sidecar reset.
##
## PR #231 keyed the "reset once per compilation" rule on file mtimes
## (`getLastModificationTime`), which cannot run in the Nim VM at macro-
## expansion time: `Error: cannot 'importc' variable at compile time; stat`.
## It fired only when the sidecar already existed, so CI (always compiling
## fresh) never caught it -- but every `nim c` of a sheds file on a machine
## with a stale sidecar died. The reset is now keyed on a {.compileTime.}
## per-file tracker; no mtime is consulted from macro code.
##
## This driver shells out to `nim c` the way the extension does:
##   1. compile a sheds file               -> sidecar has [alpha]
##   2. compile it AGAIN (sidecar exists)  -> must succeed (was the crash)
##   3. edit the source (alpha -> beta)    -> sidecar [beta], no alpha ghost
##   4. two shedsBlocks in one file        -> sidecar [gamma, delta] (merge)
##
## Run: nim c -r --hints:off --path:src --path:src/eponym tests/test_shed_sidecar_reset.nim
import os
import osproc
import strutils
import json

const RepoRoot = parentDir(parentDir(currentSourcePath()))

proc nimCmd(): string =
  let n = findExe("nim")
  doAssert n.len > 0, "nim not on PATH"
  n

proc compileSheds(src: string): tuple[ok: bool, output: string] =
  let cmd = nimCmd() & " c --hints:off --path:\"" & RepoRoot / "src" &
    "\" --path:\"" & RepoRoot / "src" / "eponym" &
    "\" -o:\"" & src.changeFileExt("") & "\" \"" & src & "\""
  let (outp, code) = execCmdEx(cmd)
  (code == 0, outp)

proc sidecarNames(nimFile: string): seq[string] =
  let (dir, base, _) = splitFile(nimFile)
  let j = parseJson(readFile(dir / (base & ".sheds.json")))
  for s in j["sheds"].elems:
    result.add(s["name"].getStr)

proc writeSrc(dir, name, body: string): string =
  result = dir / name
  writeFile(result, "import sheds_mac\n\n" & body)

proc check(cond: bool, msg: string) =
  if not cond:
    echo "FAIL: ", msg
    quit(1)
  echo "ok: ", msg

when isMainModule:
  let dir = getTempDir() / "shed_reset_regression"
  removeDir(dir)
  createDir(dir)

  # 1. First compile: sidecar has [alpha].
  let f1 = writeSrc(dir, "twice.nim", """shedsBlock:
  postulate(Int, Univ)
  proc constA(A: Univ, x: A): A = ![alpha, x]
""")
  var r = compileSheds(f1)
  check(r.ok, "first compile succeeds")
  if not r.ok: echo r.output
  check(sidecarNames(f1) == @["alpha"], "first compile sidecar = [alpha]")

  # 2. Second compile with the sidecar present: must not crash in the VM.
  r = compileSheds(f1)
  check(r.ok, "second compile (sidecar exists) succeeds")
  if not r.ok: echo r.output
  check(sidecarNames(f1) == @["alpha"], "second compile sidecar still [alpha]")

  # 3. Edit the source: the new compilation resets, no ghost of alpha.
  let f3 = writeSrc(dir, "twice.nim", """shedsBlock:
  postulate(Int, Univ)
  proc constB(A: Univ, x: A): A = ![beta, x]
""")
  r = compileSheds(f3)
  check(r.ok, "recompile after edit succeeds")
  if not r.ok: echo r.output
  check(sidecarNames(f3) == @["beta"], "edited source resets: sidecar = [beta], no ghost")

  # 4. Two shedsBlocks in one compilation merge.
  let f4 = writeSrc(dir, "twoblocks.nim", """shedsBlock:
  postulate(Int, Univ)
  proc constA(A: Univ, x: A): A = ![gamma, x]

shedsBlock:
  postulate(Bool, Univ)
  proc constB(A: Univ, x: A): A = ![delta, x]
""")
  r = compileSheds(f4)
  check(r.ok, "two-block compile succeeds")
  if not r.ok: echo r.output
  let names4 = sidecarNames(f4)
  check(names4.len == 2 and "gamma" in names4 and "delta" in names4,
    "two shedsBlocks in one compilation merge: " & names4.join(","))

  removeDir(dir)
  echo "ALL SIDECAR RESET CHECKS PASSED"
