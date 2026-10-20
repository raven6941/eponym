import eponym_mac

eponymBlock:
  postulate(Thing, Univ)
  proc identity(thing: Thing): Thing = thing

discard identity("a host string is not an explicit Thing codec")
