## The REPL's WHNF printer handles values introduced by the runtime bridge.

import std/tables
import eponym_init
import repl

when isMainModule:
  let rendered = prettyWhnf(toHostValue("opaque"), initTable[int, string]())
  doAssert rendered == "<opaque Nim value: string>"
  echo "test_repl_values: opaque host values have a readable representation"
