# Records with named projections (Issue #37), embedded.
#
# `record Pt:` desugars to a transparent iterated-Sigma def, a positional
# constructor `mkPt`, and named projections `Pt.x` / `Pt.y`, with `p.x`
# dot notation resolved against the record table at elaboration time.
# The Eponym side builds points, projects, and computes with the fields;
# the Nim driver below calls the elaborated procs directly -- compiling
# this file IS the typecheck (a bad projection is a compile error).

import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)

  record(Pt):
    field(x, Int)
    field(y, Int)

  # Sum of coordinates: constructor + both projections, evaluated.
  proc normSum(x: Int, y: Int): Int =
    addInt((mkPt(x, y)).x, (mkPt(x, y)).y)

  # Translate then re-project: projections compute through the Sigma.
  proc movedX(x: Int, y: Int, dx: Int): Int =
    (mkPt(addInt(x, dx), y)).x

  # A point is just its fields: swapping twice is the identity on x.
  proc swapSwapX(x: Int, y: Int): Int =
    (mkPt((mkPt(x, y)).y, (mkPt(x, y)).x)).x

# --- Normal Nim program using the Eponym-checked definitions --------------
proc main() =
  echo "records: named projections over a desugared Sigma, embedded."
  doAssert normSum(3, 4) == 7
  doAssert movedX(3, 4, 10) == 13
  doAssert swapSwapX(3, 4) == 4
  echo "  normSum(3,4) = 7, movedX(3,4,10) = 13, swapSwapX(3,4) = 4"

main()
