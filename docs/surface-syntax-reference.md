# Eponym surface-syntax reference

The surface grammar is one grammar: what you write in a standalone `.ep`
file and what you write inside `eponymBlock:` in Nim are the same language
(issue #144; conformance is pinned by `tests/surface_conformance.nim`, and
the Nim-side mapping for every form is pinned by
`tests/test_embedded_macro_forms.nim`). The canonical grammar lives in
`src/eponym/parse_surf.nim`:

```
decl    = proc | def | postulate | elim | red | data | record | import
term    = ... Pi | Sig | lam | let | ascription | application | ? | Nat literals ...
```

Trust-model note: this document describes the syntax. What each construct
*guarantees* (and the known soundness gaps) is in `docs/trust-model.md`.

## Entering: `eponymBlock`

```nim
import eponym_mac
import eponym_embed

eponymBlock:
  import "../../lib/nat.ep"

  data(Session, Univ):
    proc sendS(A: Univ, s: Session): Session
```

The macro converts the Nim AST block to Eponym source text, feeds it to the
canonical string parser, elaborates at Nim compile time, and generates
wrapper procs. Elaboration failures become Nim compiler errors. Standalone
`.ep` files skip the macro and go straight to the parser; the syntax is
identical.

## Declarations

### `data` — indexed datatypes

```nim
data(NatD, Univ):
  proc zeroD(): NatD
  proc sucD(n: NatD): NatD
```

The first argument is the index type (`Univ` = `?` for unindexed types;
`Session -> Univ` for a type indexed by a session, as in
`examples/embedded/session_types.nim`). Constructors are declared with
`proc` inside the block; indices in the return type must be supplied
(`proc mkChan(s: Session): Chan(s)`). `data` desugars to
postulate/elim/red; the kernel motive-validates every generated iota rule
(see trust model). There is **no positivity check** (issue #33).

### `elim` / `red` — manual eliminators and computation rules

`data` generates these, but you can write them directly (Experiment 4):

```nim
elim(boolElim, Pi(C: Bool -> Univ, C(true) -> C(false) -> Pi(b: Bool, C(b))))
red(boolElim(C, t, f, true), t)
red(boolElim(C, t, f, false), f)
```

(from `tests/test_embedded_macro_forms.nim`). The elaborator rejects
non-structurally-recursive `red` rules at declaration time (issue #36).

### `def` — clause-style definitions

```nim
def(isZeroD, NatD -> NatD):
  clause([zeroD], zeroD)
  clause([sucD(n)], zeroD)
```

(from `tests/test_embedded_macro_forms.nim`). Each `clause([patterns], rhs)` becomes one defining equation. Coverage and
termination of clause definitions are checked (issues #78, #36).

### `proc` — function definitions

```nim
proc addD(x: NatD, y: NatD): NatD =
  natElim(lam(_: NatD, NatD), x, lam(n: NatD, r: NatD, sucD(r)), y)
```

`proc name(args): Ret = body`. Bodies are ordinary terms; `by` tactics (below)
may discharge the whole body.

### `postulate` — axioms

```nim
postulate(sendNat, Pi(x: Nat, ch {.linear.}: Chan(sendS(Nat, endS())), Chan(endS())))
```

`postulate` asserts a type with no evidence — it is an axiom. Machine `Int`
and its primops are kernel axioms; a `postulate`d primop that lies
poisons every proof touching it (trust model).

### `record` — records (#37)

```nim
record(Pt):
  field(x, Int)
  field(y, Int)
```

(from `examples/embedded/records.nim`). Fields are declared with `field`;
construction is `mkPt(x, y)`, projection is `p.x`.

### `import`

```nim
import "../../lib/nat.ep"
```

Imports a prelude/stdlib file by path (issue #131): `lib/nat.ep`,
`lib/bool.ep`, `lib/list.ep`, `lib/vec.ep`, `lib/nat_lemmas.ep`. The
standalone grammar and the embedded form are the same statement.

### `interface` / `command` — ambient abilities (#177)

```nim
interface Console
command putStr : Str -> Unit in Console
```

Frank-style ambient abilities threaded through `check`/`infer` at
elaboration time only — they never appear in the object program.

## Types and terms

### The universe: `?` (spelled `Univ`)

Type-in-Type, known-inconsistent; the honest policy is "don't write
Girard's paradox" (issue #52, trust model). `Nat : ?`, `? : ?`.

### Dependent functions: `Pi`

```nim
Pi(x: Nat, ch {.linear.}: Chan(sendS(Nat, endS())), Chan(endS()))
Pi(C: Bool -> Univ, C(true) -> C(false) -> Pi(b: Bool, C(b)))
```

Binders are `(name : Type)`; the final position is the codomain.
Non-dependent arrows are sugar: `A -> B` is `Pi(_: A, B)`.
**Implicit binders** use braces: `Pi {A : Univ} (x : A). A` — solved by
Miller-pattern unification at use sites.

### Dependent pairs: `Sig`

```nim
postulate(recvNat, Pi(ch {.linear.}: Chan(recvS(Nat, endS())), Sig(x: Nat, Chan(endS()))))
```

`Sig(x: Nat, Chan(endS()))` is the pair type; `fst(p)` / `snd(p)` project
(as in `server` in `examples/embedded/session_types.nim`).

### Lambdas: `lam`

```nim
lam(x: Nat, addInt(x, x))
lam(_: NatD, NatD)          # the motive in an eliminator call
```

### `let` (typed)

```nim
let p = recvNat(ch)
```

in `server`: binds `p` in the rest of the body. Ascriptions work too:
`(t : T)` checks `t` against `T`.

### Quantities (QTT, issues #64/#66)

Binders carry a quantity: `q1` linear (use exactly once), `q0` erased (never
use), `qω` unrestricted (default, unchecked). In `eponymBlock` the
Nim-side spelling is a pragma:

```nim
proc client(ch {.linear.}: Chan(sendS(Nat, endS()))): Chan(endS()) =
  sendNat(zero(), ch)
```

`ch {.linear.}` becomes `(1 ch : ...)`; the elaborator rejects using a
linear variable zero or two-plus times. Types are checked in the all-0
context, so a type-level mention of a linear variable does not consume it.
In canonical surface text the spellings are `(1 x : T)` (linear),
`(0 x : T)` (erased), `(q x : T)` (quantity variable, issue #66).

### Natural numbers

Integer literals in term position elaborate to `suc^n(zero)`; `1` in *type*
position lexes as the unit type. The unit value is `<>`.

### Tactics: `by`

```nim
proc pf1(): Eq(Int, 42, 42) = byTac(refl)
proc idInt(x: Int): Int = byTac(assumption)
```

A `by <tactic>` body is discharged by an elaboration-time tactic term.
`tac` names resolve to registered tactics (`refl`, `assumption`, the
`natArithHandler` behind `by arith` for linear Nat equations, ...).
Conversion-handler effects fire at macro expansion/compile time, never in
the object program; evidence is revalidated LCF-style with handlers
uninstalled (issue #41, trust model).

### Equality

`Eq(A, x, y)` is propositional equality; `refl` proves `Eq(Int, 42, 42)`.
(#66-era core.)

## What's deliberately missing

- No positivity check on `data` (#33) — negative occurrences are your
  problem.
- No universe hierarchy (#52) — `? : ?`.
- Termination: single-function structural recursion only (#36); mutual
  recursion (#42) and looping type-level programs are the author's problem.
- Implicit-binder *lambdas* have no Nim-side spelling (parser note,
  issue #151): `{x : T}` in expression position would collide with the
  Pi-implicit table syntax, and no corpus code needs it.

## Further reading

- `docs/trust-model.md` — what the system checks vs. what is your problem.
- `docs/staging-design.md`, `docs/layers.md` — architecture (staging is
  experimental; `src/experimental/` holds code not on production paths).
- The `examples/embedded/` corpus — every form above appears in a compiling
  example; the tutorial (`docs/tutorial.md`, issue #184) walks through
  them in order.
