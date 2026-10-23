import eponym_mac

eponymBlock:
  requireCompiled()
  postulate(Int, Univ)
  postulate(Nat, Univ)
  runtimeType(Int, int)
  runtimeType(Nat, int)
  # A quantity-0 function domain has no host representation (its argument
  # is erased at every call site), so the repr tier honestly rejects it.
  # (First-order function domains like `Int -> Int` compile to
  # `{.closure.}` proc types since issue #407 slice 3; `f` is used here so
  # its quantity stays ω and the q0 domain reaches the signature check.)
  proc applyQ0(f: Pi(p {.erased.}: Nat, Int), x: Int): Int = f 0
