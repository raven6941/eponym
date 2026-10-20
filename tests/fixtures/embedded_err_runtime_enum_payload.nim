import eponym_mac
import eponym_embed

type MaybeCode = enum
  hasCode, noCode

eponymBlock:
  postulate(Int, Univ)
  data(Maybe, Univ):
    proc hasCode(value: Int): Maybe
    proc noCode(): Maybe
  runtimeType(Maybe, MaybeCode)
  proc maybeIdentity(value: Maybe): Maybe = value
