## Issue #221 follow-up: sidecar ghost elimination test (mtime-based reset).
##
## Each run simulates ONE shedsBlock expansion: it writes the given shed
## names via writeShedSidecar, then prints the sidecar's names.
##
## Shell protocol:
##   run1: write [alpha beta]          -> sidecar [alpha, beta]
##   touch source (simulate edit)
##   run2: write [beta gamma]          -> sidecar [beta, gamma] (no alpha ghost)
##   run3: write [delta] (no touch)    -> sidecar [beta, gamma, delta] (merge)
##
## Run: nim c -r --hints:off --path:src --path:src/eponym tests/test_shed_sidecar_reset.nim <names...>
import json
import os
import strutils
import sheds

const TestFile = "/tmp/shed_reset_test.nim"
const Sidecar = "/tmp/shed_reset_test.sheds.json"

proc mkShed(name: string): ShedInfo =
  ShedInfo(name: name, draft: "", nimLine: 1, nimCol: 1,
           holeLine: 1, holeIdx: 0, holeCol: 1, genSrc: "test",
           goal: "Nat", ctx: @[], goalPi: @[], status: ssYellow)

proc main() =
  # Ensure the "source" exists so mtime comparison works.
  if not fileExists(TestFile):
    writeFile(TestFile, "# fake source\n")
  var sheds: seq[ShedInfo] = @[]
  for i in 1 ..< paramCount() + 1:
    sheds.add(mkShed(paramStr(i)))
  writeShedSidecar(TestFile, sheds)
  let j = parseJson(readFile(Sidecar))
  var names: seq[string] = @[]
  for e in j["sheds"].elems:
    names.add(e["name"].getStr)
  echo names.join(",")

when isMainModule:
  main()
