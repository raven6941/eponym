# Choosing your Eponym↔Nim boundary mechanism

When an Eponym definition must cross into Nim — or a Nim value or operation
must cross into checked code — one mechanism from the boundary vocabulary is
the right tool. Follow the questions top-down and take the first branch
whose answer is "yes". Each question names how to recognize its own answer;
each leaf links to the reference that documents the mechanism. The
[surface-syntax reference](surface-syntax-reference.md#the-nim-boundary)
documents the pieces; this page is the entry point, not the reference.

## The tree

**0. Which direction does the value move?**

- Checked Eponym definition → called from ordinary Nim: Eponym attempts to
  generate a direct Nim wrapper. If its type has a supported runtime
  representation, call the generated proc normally. If not, compilation
  reports that the definition checked successfully but has no callable Nim
  representation; use an appropriate mapping/codec or mark it
  `compileTimeOnly`.
- Ordinary Nim → checked Eponym code, or a shared type crossing both ways:
  continue below.

**1. Do you want it type-checked with no runtime API at all?**

If the definition exists only to be verified — a lemma, a spec, a protocol
skeleton whose runtime roles live elsewhere — you don't need a boundary,
you need its absence. → `compileTimeOnly(checkedDefinition)`
([reference](surface-syntax-reference.md#the-nim-boundary)).

How to tell: if nobody may ever call it from Nim and no wrapper should
exist, this is your answer. Proof/type-level-only content (erased `q0`
arguments) typically lands here.

**2. Does it already have a representation?**

Primitives `Int`, `Nat`, `Bool` and explicit binders (`[n: Nat]` →
`static[int]`) cross with built-in codecs — no declaration needed. The
canonical `Vec`/`List`/`Option` families opt into their sequence codecs
with one call (`runtimeVector`, `runtimeList`, `runtimeOption`);
non-dependent `Sig` and plain records map structurally. →
nothing extra / structural mapping
([reference](surface-syntax-reference.md#the-nim-boundary)).

How to tell: if your type is built from these primitives and canonical
families, stop here. If a family has the canonical `nil`/`cons` or
`none`/`some` shape but no built-in codec, the next question applies.

**3. Is the value opaque — Eponym never looks inside it?**

If Eponym only passes the value between host operations and never
pattern-matches, projects, or computes on it, it is a box with a Nim type
inside. → `runtimeType(EponymType, NimType)`
([reference](surface-syntax-reference.md#the-nim-boundary)).

How to tell: search the checked code for any eliminator or case split on
the value. If there is none, and Nim code constructs, consumes, and
transforms it, it is opaque. Indices on mapped families are still checked;
only the payload representation is trusted. (The session-types `Channel`
example in the reference is this shape.)

**4. Does Eponym inspect the value's structure, or does Nim need a specific
representation?**

If the value crosses in a Nim shape you choose (a `seq[int]`, a custom
object, a packed format) and Eponym constructors must map onto it
faithfully, you own the encode/decode pair. →
`runtimeCodec(Type, NimType, encode, decode)`
([reference](surface-syntax-reference.md#the-nim-boundary)).

How to tell: this is question 3's complement. If Eponym pattern-matches the
value *and* no built-in or structural mapping (question 2) covers it, you
write the codec. The implementation is trusted — validate indices and throw
`ValueError` on malformed host values.

**5. Is it a Nim operation called from checked code?**

A host effect, library call, or primitive that checked code invokes through
a declared contract. → `postulate` + `bindPostulate` (or
`bindPostulateMutable` for `var` parameters, `bindPostulatePair` for
pair-returning callbacks; dependent-pair results need the explicit
`bindPostulatePairTrusted` / `runtimeRecordTrusted` / `runtimePairTrusted`
opt-ins)
([reference](surface-syntax-reference.md#bindpostulate--trusted-runtime-adapter)).

How to tell: the arrow points the other way from question 0 — the
*implementation* lives in Nim and checked code *calls* it. The Eponym
signature is checked against the Nim proc's type; the body's behavior is
trusted. A reachable runtime postulate with no host binding is rejected
with a diagnostic naming the missing binding.

**6. Does the runtime type itself depend on a runtime index?**

If a runtime value selects the *shape* of a type that runtime code must
inspect — a `PrintfType format` argument chain, a generic serializer —
erasure and codecs are the wrong tools: the type structure is computed at
runtime. → `{.stagedType.}` on the type-level family
([design](staged-inject-design.md)).

How to tell: ask whether knowing the value at compile time would change
which Nim types the wrapper mentions. If yes and the value is genuinely
dynamic, no codec can express it — the stager compiles the type-level
program into a residual `TypeRep` function. This is the Tier 2 escape hatch;
Tier 1 (questions 2–4) covers the overwhelmingly common case.

**Check before you commit.** Annotate a definition with `{.boundaryPreview.}`
to print the boundary the compiler will generate — the Nim signature and
the runtime checks — before codegen runs. It changes nothing; it shows you
what you chose.

## Cross-cutting notes

- Every mechanism leaves something to Nim; `trust-model.md` names exactly
  what the checker guarantees and what stays your problem.
- Current coverage gaps live in `known-limitations.md` — check there before
  designing around a missing shape.
- The `-d:eponymTrustReport` build flag prints a compile-time inventory of
  the block's explicit trust boundaries for review.
- Sheds (hole-driven development) are editor objects under `eponymBlock`
  use-gating, not boundary mechanisms; they are not part of this tree.
