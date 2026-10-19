import ../../src/eponym/eponym_mac

proc hostNestedSigma(seed: int): tuple[a, b, c: int] =
  (seed, seed, seed)

eponymBlock:
  import "runtime_imported_nested_sigma.ep"
  bindPostulate(makeNestedSigma, hostNestedSigma, Int,
    Sig(a: Int, Sig(b: Int, Int)))
  proc badNestedSigmaAdapter(seed: Int): Sig(a: Int, Sig(b: Nat, Int)) =
    makeNestedSigma(seed)
