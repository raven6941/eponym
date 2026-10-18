import eponym_mac
import eponym_embed

eponymBlock:
  import "../../lib/bool.ep"
  postulate(Int, Univ)
  proc unsupportedIf(): Int =
    if true: addInt(1, 0)
    elif false: addInt(2, 0)
