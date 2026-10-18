import eponym_mac
import eponym_embed

eponymBlock:
  import "../../lib/vec.ep"
  proc dependentSigmaId(value: Sig(n: Nat, Vec[Nat, n])):
      Sig(n: Nat, Vec[Nat, n]) = value

discard dependentSigmaId((1, 2))
