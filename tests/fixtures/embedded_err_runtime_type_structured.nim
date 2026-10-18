import eponym_mac

type PointHandle = object
  x: int

eponymBlock:
  postulate(Int, Univ)
  record(Point):
    field(x, Int)
  runtimeType(Point, PointHandle)
  proc project(point: Point): Int = point.x
