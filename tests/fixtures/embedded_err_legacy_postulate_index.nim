import eponym_mac

eponymBlock:
  import "../../lib/vec.ep"
  import "legacy_postulate_index.ep"

  proc oldIndexedHead(values: Vec[Nat, 0]): Vec[Nat, 0] =
    indexedHead(zero(), values)
