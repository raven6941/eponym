import eponym_mac

eponymBlock:
  data(LocalToken, Univ):
    proc localToken(): LocalToken
  def(tokenIdentity, LocalToken -> LocalToken):
    clause([localToken], localToken)

discard tokenIdentity(1)
