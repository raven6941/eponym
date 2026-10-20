import eponym_mac
import eponym_embed

type RuntimePoint = object
  length: int
  values: seq[int]

eponymBlock:
  import "../../lib/nat.ep"
  import "../../lib/vec.ep"
  record(Point):
    field(length, Nat)
    field(values, Vec(Nat, length))
  runtimeType(Point, RuntimePoint)
  proc pointId(value: Point): Point = value

discard pointId(RuntimePoint(length: 2, values: @[1, 2]))
