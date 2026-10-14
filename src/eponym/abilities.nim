## Issue #177: ambient abilities (Frank-style) for the elaborator.
##
## An ability is an ordered snoc-list of interface names with an optional
## open tail:
##   Ability ::= ifaces: seq[string], tail: closed | ?aN
## The rightmost interface shadows (Frank's snoc-list semantics). A closed
## ability is written `[I1, I2]`; an open one `[I1, ?a3]` or just `[?a3]`.
## `nil` is the empty closed ability `[]` (fast path: pure code allocates
## nothing).
##
## Frank's invariance ("no subeffecting, no row unification") is the point:
## abilities compare by *syntactic* equality after zonking. Open tails are
## ability metavariables, solved only by one-directional instantiation
## (the operator's peg variable is instantiated *to* the ambient; the
## ambient's variables are rigid for this purpose).

type
  Ability* = ref object
    ## Invariant: either `tailOpen` (an ability metavariable; `ifaces` is
    ## always empty for freshened signature pegs) or closed.
    ifaces*: seq[string]
    tailOpen*: bool
    tailId*: int          # valid iff tailOpen

proc abClosed*(ifaces: seq[string] = @[]): Ability =
  ## A closed ability. `abClosed()` is `[]`; `nil` means the same thing and
  ## is preferred on hot paths.
  if ifaces.len == 0: return nil
  Ability(ifaces: ifaces, tailOpen: false, tailId: 0)

proc abOpen*(id: int): Ability =
  ## An open ability consisting of a single ability metavariable `?a<id>`.
  Ability(ifaces: @[], tailOpen: true, tailId: id)

proc abIsEmpty*(ab: Ability): bool =
  ## Syntactic `[]`: nil or a closed ability with no interfaces.
  ab.isNil or (not ab.tailOpen and ab.ifaces.len == 0)

proc abEqual*(a, b: Ability): bool =
  ## Syntactic equality (Frank invariance): same interfaces in order, and
  ## tails that are both closed or the *same* open variable. Solved
  ## variables must be zonked before calling.
  if abIsEmpty(a): return abIsEmpty(b)
  if abIsEmpty(b): return false
  if a.ifaces != b.ifaces: return false
  if a.tailOpen != b.tailOpen: return false
  if a.tailOpen: return a.tailId == b.tailId
  true

proc pegCompatible*(opPeg, ambient: Ability): bool =
  ## Frank-style peg compatibility as a pure predicate (no mutation, no
  ## solving): an open peg is compatible with any ambient; a closed peg
  ## requires syntactic equality with the ambient (invariance — no
  ## subeffecting, no effect inference). `nil` is `[]`.
  if opPeg.isNil or abIsEmpty(opPeg): return abIsEmpty(ambient)
  if opPeg.tailOpen: return true
  abEqual(opPeg, ambient)

proc `$`*(ab: Ability): string =
  if ab.isNil: return "[]"
  result = "["
  var first = true
  for i in ab.ifaces:
    if not first: result &= ", "
    result &= i
    first = false
  if ab.tailOpen:
    if not first: result &= ", "
    result &= "?a" & $ab.tailId
  result &= "]"

proc abSnoc*(ab: Ability, iface: string): Ability =
  ## Extend a closed ability on the right (shadowing). Open abilities are
  ## never extended in the prototype (no row unification, per Frank).
  if abIsEmpty(ab): return abClosed(@[iface])
  assert not ab.tailOpen, "abSnoc on an open ability"
  abClosed(ab.ifaces & @[iface])
