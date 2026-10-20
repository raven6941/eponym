import eponym_mac
import eponym_embed
import elab
import eponym_init

proc wrongTreeEncoder(value: int, globals: Globals): Value =
  intToValue(value)

proc treeDecoder(value: Value, globals: Globals): seq[int] =
  @[]

eponymBlock:
  postulate(Int, Univ)
  data(Tree, Univ):
    proc treeEmpty(): Tree
    proc treeNode(value: Int, tail: Tree): Tree
  runtimeCodec(Tree, seq[int], wrongTreeEncoder, treeDecoder)
  proc identity(value: Tree): Tree = value

discard identity(@[1, 2, 3])
