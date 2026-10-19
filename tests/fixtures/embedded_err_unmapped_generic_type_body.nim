import eponym_mac
import eponym_embed
import eponym_init
import elab

eponymBlock:
  import "../../lib/vec.ep"
  runtimeVector(Vec)
  proc genericEmpty[A: Univ](): Vec[A, zero] = vecnil[A]()
  runtimeValue(genericEmpty)

discard genericEmpty()
