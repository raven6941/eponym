## bench_conv_cache.nim — Issue #41: conversion-heavy cache benchmark at scale.
##
## The acceptance test in elab.nim showed the cache handler matching the
## default handler on a 6-decl Vec corpus, but the corpus was too small
## for the cache to win (default 0.038s vs cache 0.035s). This benchmark
## scales the corpus up and asks the real question: does the scoped
## cacheConvHandler pay off on conversion-heavy elaboration?
##
## Corpus design: many near-identical declarations that force repeated,
## expensive conversion goals:
##   - vappend of literal vectors with large indices: the ascribed
##     `Vec Nat (suc^k zero)` must convert against inferred
##     `Vec Nat (add m n)`, costing m fireRed steps + areEqual over
##     large unary numerals — the same goal shape recurs per size class;
##   - `by refl` proofs of large ground add equations (add A B ≡ suc^C),
##     identical goals repeated.
## A second "distinct" corpus varies every numeral. In practice it is not
## the worst case the name suggests: even with all-distinct numerals,
## ~99% of conversion goals still repeat (clause-elaboration motives,
## implicit insertion, and ascription checks recur structurally), so the
## measured delta mostly reflects probe overhead on hits rather than
## misses. Observed: 98.8% hit rate, 1.01x.
##
## Fairness: both sides elaborate the same generated string (parsing is
## identical and inside the timed region on both sides, so it dilutes
## but cannot bias the delta). Accept/reject identity is asserted on
## declaration names. Hit/miss counters wrap the cache handler.
##
## Usage: nim c -r --hints:off --path:src src/bench_conv_cache.nim

import elab
import unify
import ett_init   # Term for the counting wrapper
import preterm    # Loc for the counting wrapper
import times
import strformat

proc numLit*(n: int): string =
  ## unary numeral suc^n zero as surface syntax. Each level is
  ## parenthesized — `(suc (suc zero))`, not `suc (suc zero)` — because
  ## in argument position the surface parser reads juxtaposition as
  ## application, so an unparenthesized `suc` would become a bare
  ## argument (this bit us in the benchmark corpus).
  result = "zero"
  for _ in 1 .. n:
    result = "(suc " & result & ")"

proc litVec*(n: int): string =
  ## literal vector of n zeros. cons's telescope is
  ## (n : Nat) (x : A) (xs : Vec A n): the n argument is the TAIL length,
  ## so level i passes numLit(i-1).
  result = "(nil Nat)"
  for i in 1 .. n:
    result = "(cons Nat " & numLit(i - 1) & " zero " & result & ")"

const Preamble* = """
data Nat : ? where
| zero : Nat
| suc (n : Nat) : Nat
data Eq (A : ?) (x : A) : A -> ? where
| refl : Eq A x x
def add : Nat -> Nat -> Nat
| zero n = n
| (suc m) n = suc (add m n)
data Vec (A : ?) : Nat -> ? where
| nil : Vec A zero
| cons (n : Nat) (x : A) (xs : Vec A n) : Vec A (suc n)
def vappend : Pi {A : ?}. Pi {m : Nat}. Pi {n : Nat}. Vec A m -> Vec A n
  -> Vec A (add m n)
| nil ys = ys
| (cons k x xs) ys = cons A (add k n) x (vappend xs ys)
"""

proc buildRepeated*(reps: int): string =
  ## Same size classes recur: identical conversion goals recur.
  result = Preamble
  let classes = @[(12, 12), (20, 8), (16, 16)]
  var k = 0
  for r in 0 ..< reps:
    for (m, n) in classes:
      result &= &"proc w{k} : Vec Nat ({numLit(m + n)}) = vappend {litVec(m)} {litVec(n)}\n"
      inc k
  for r in 0 ..< reps:
    result &= &"proc e{r} : Eq Nat (add {numLit(25)} {numLit(25)}) ({numLit(50)}) = by refl\n"

proc buildDistinct*(reps: int): string =
  ## Every numeral unique: no goal repeats (worst case for the cache).
  result = Preamble
  var k = 0
  for r in 0 ..< reps:
    let m = 10 + (r mod 15)
    let n = 10 + ((r * 7) mod 15)
    result &= &"proc w{k} : Vec Nat ({numLit(m + n)}) = vappend {litVec(m)} {litVec(n)}\n"
    inc k
    let a = 20 + (r mod 11)
    let b = 20 + ((r * 5) mod 11)
    result &= &"proc e{k} : Eq Nat (add {numLit(a)} {numLit(b)}) ({numLit(a + b)}) = by refl\n"
    inc k

type Counters = ref object
  hits, misses: int

proc countingCache(c: Counters): ConvHandler =
  ## cacheConvHandler wrapped with hit/miss counters.
  let inner = cacheConvHandler()
  let decide: ConvDecide =
    proc(ms: var MetaStore, s: var Supply, a, b: Term, loc: Loc,
         ctxLen: int): ConvVerdict {.closure.} =
      let v = inner.decide(ms, s, a, b, loc, ctxLen)
      if v == cvDischarged: inc c.hits
      else: inc c.misses
      v
  ConvHandler(decide: decide, coreValid: true)

proc runCorpus(name: string, corpus: string, rounds: int) =
  echo "=== " & name & " (" & $corpus.len & " chars) ==="
  var tDefault = 0.0
  var tCache = 0.0
  var names0: seq[string] = @[]
  for r in 0 ..< rounds:
    let t0 = cpuTime()
    let defs0 = elabCheck(corpus)
    tDefault += cpuTime() - t0
    if r == 0:
      for d in defs0: names0.add(d.name)
    var c = Counters()
    let t1 = cpuTime()
    let defs1 = elabCheck(corpus, @[countingCache(c)])
    tCache += cpuTime() - t1
    assert defs1.len == names0.len, "decl count changed with cache handler"
    for i in 0 ..< names0.len:
      assert defs1[i].name == names0[i], "decl name changed with cache handler"
    if r == 0:
      let total = c.hits + c.misses
      let rate = if total > 0: 100.0 * c.hits.float / total.float else: 0.0
      echo &"  cache goals: {total} (hits {c.hits}, misses {c.misses}, hit rate {rate:.1f}%)"
  tDefault /= rounds.float
  tCache /= rounds.float
  let speedup = if tCache > 0: tDefault / tCache else: 0.0
  echo &"  default: {tDefault:.3f}s   cache: {tCache:.3f}s   speedup: {speedup:.2f}x"
  echo &"  decls: {names0.len}, accept/reject identical"

when isMainModule:
  const Rounds = 2
  const Reps = 15
  runCorpus("repeated-goals", buildRepeated(Reps), Rounds)
  runCorpus("distinct-goals", buildDistinct(Reps), Rounds)
