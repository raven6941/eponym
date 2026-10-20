## Exercise the checked Paxos roles over their real loopback adapter.
import std/[os, strutils]
import falsify
import ../examples/embedded/paxos_session as paxos

when isMainModule:
  if paramCount() == 3 and paramStr(1) == "--paxos-acceptor":
    paxos.runPaxosAcceptor(parseInt(paramStr(2)), parseInt(paramStr(3)))
  else:
    var rng = initRng(917231'u64)
    let rounds = forAll("checked Paxos roles preserve the promised value",
      rng, 40,
      proc(r: var Rng): int = r.genInt(0, 100000),
      proc(seed: int): bool =
        let ballot = seed mod 1000
        let stored = (seed div 7) mod 1000
        paxos.runPaxosRound(ballot, stored) == stored,
      shrinkInt)
    if not rounds:
      quit(1)
