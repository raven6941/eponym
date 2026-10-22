## Compile-time benchmark fixture: import the proof-carrying Nat lemma corpus
## through the same Nim macro boundary users exercise with `eponymBlock`.
import eponym_mac

eponymBlock:
  import "../lib/nat_lemmas.ep"
