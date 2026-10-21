import eponym_mac
import eponym_embed

eponymBlock:
  import "../../lib/nat_to_int.ep"
  proc implicitConversion(value: Nat): Int = value
