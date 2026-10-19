import eponym_mac
import eponym_embed
import eponym_init
import elab

eponymBlock:
  data(Token, Univ):
    proc tokenValue(): Token
  proc tokenIdentity[token: Token](): Token = token
  runtimeValue(tokenIdentity)

discard tokenIdentity("no mapped Token representation")
