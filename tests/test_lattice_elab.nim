## #170 acceptance: the lattice-monotone prototype agrees with the expected
## verdicts on the full Vec-fragment corpus (same 16 cases as
## bench_elab_end_to_end.nim), and the rebuilt output matches the input
## term on acceptance (output determination smoke test).
##
## Usage: nim c -r --path:src --path:src/eponym --path:src/experimental/relational \
##   --path:src/experimental/staging tests/test_lattice_elab.nim

import minikanren
import lattice_elab
import vec_corpus
import options

var fails = 0
for c in vecCorpus():
  let r = checkLatTop(c.tm, c.ty, c.ctx)
  if r.ok != c.expect:
    echo "MISMATCH: ", c.name, " expected ", c.expect, " got ", r.ok
    if r.failure.isSome: echo "  ", r.failure.get
    inc fails
  else:
    if c.expect:
      # Output determination: rebuild from the converged state == input.
      if $r.output != $c.tm:
        echo "OUTPUT MISMATCH: ", c.name
        echo "  rebuilt: ", r.output
        echo "  input:   ", c.tm
        inc fails
      else:
        echo "ok: ", c.name, " (accept, output rebuilt)"
    else:
      if r.failure.isNone:
        echo "MISSING PROVENANCE: ", c.name, " rejected without a reason"
        inc fails
      else:
        echo "ok: ", c.name, " (reject: ", r.failure.get, ")"
if fails > 0:
  echo fails, " FAILURES"
  quit(1)
echo "all ", vecCorpus().len, " cases agree"
