import eponym_mac
import eponym_embed

eponymBlock:
  import "../../lib/float.ep"
  import "../../lib/text.ep"
  postulate(scaleFloat, Float -> Float)
  proc badScale(value: String): Float = scaleFloat(value)
