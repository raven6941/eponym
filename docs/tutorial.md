# Eponym tutorial

From zero to a compile-time-checked dependent type in about 15 minutes.

Eponym is a dependently-typed language *embedded* in Nim: you write
type-checked definitions inside an `eponymBlock`, and ordinary Nim code
calls them. This tutorial takes you from installation to your first
checked dependent type to one motivating example of why dependent types
earn their keep. Every snippet below compiles as shown (each was
machine-checked while writing this document).

You will need Nim >= 2.0 (built with 2.2.12 via
[choosenim](https://github.com/dom96/choosenim)) and `nimble`.

## 1. Install

```sh
nimble install eponym        # from the nimble package directory (once published)
# or, from a checkout of this repo:
nimble install
```

This installs the elaborator modules and the Eponym prelude (`lib/*.ep`:
`Nat`, `Vec`, `Eq`, lists, …) into the nimble package directory. Set up
a project like this:

```
myproject/
  hello.nim
  lib/            <- copy the prelude files you need here,
                     from ~/.nimble/pkgs2/eponym-*/lib/
```

`import "x.ep"` inside an `eponymBlock` resolves relative to the Nim file
containing the block, so you vendor the prelude files your project uses
next to it.

## 2. Hello, checked world

`hello.nim`:

```nim
import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)

  proc double(x: Int): Int =
    addInt(x, x)

echo double(21)
```

```sh
nim c -r hello.nim
# 42
```

What just happened:

- `eponymBlock:` is a macro. It converts the block to Eponym source,
  **elaborates it at Nim compile time** (inside the macro, running in
  Nim's VM), and generates a wrapper proc per definition. Ordinary Nim
  code then calls `double` like any other proc.
- Nim syntax inside the block is notation for Eponym, not arbitrary host
  Nim. The macro does not execute Nim library calls, IO, loops, or mutation
  inside checked definitions. The current boundary is listed in the
  [surface-syntax reference](surface-syntax-reference.md).
- `postulate(Int, Univ)` takes `Int` as given (`Univ` is Nim-friendly
  syntax for `Type 0`). Universes are explicit: `Type 0 : Type 1 : ...`.
  In surface syntax, `?` introduces a hole to fill, and `_` discards a
  binder or pattern. The full story is in
  [the surface-syntax reference](surface-syntax-reference.md). `addInt`
  is a primitive integer operation.
  The prelude (`lib/nat.ep`) defines `Nat` inductively instead — we will
  use it in the next section.
- A call like `double(21)` re-elaborates the block on its first runtime call
  (then uses the cache) and evaluates the checked term. Generated wrappers
  support first-order `Int`/`Nat` and explicitly mapped opaque postulated
  types; other definitions are still checked at compile time.
- This partial runtime bridge is a known limitation, not a limit on
  what the elaborator can check. See [known limitations](known-limitations.md)
  and the [postulate binding experiment](postulate-nim-binding-experiment.md)
  for the path toward callable Nim-backed operations.

Now break it. Change the body to `addInt(x, y)` and recompile:

```
hello_bad.nim(5, 3) Error: eponymBlock elaboration error: line 2, col 40: unbound variable 'y'
```

Type errors inside the block are Nim compiler errors pointing at your
code — elaboration failures never crash the compiler, they are reported
like any other compile error.

## 3. Your first dependent type: length-indexed vectors

A *dependent* type is a type that mentions a value. The classic example
is vectors indexed by their length: `Vec(A, n)` is the type of vectors
with elements in `A` and length exactly `n`. It lives in the prelude —
no need to define it yourself.

`vecs.nim` (with `lib/vec.ep` and `lib/nat.ep` vendored under `lib/`):

```nim
import eponym_mac
import eponym_embed

eponymBlock:
  import "lib/vec.ep"

  # A 2-vector, with its length in the type.
  proc twoNats(x: Nat, y: Nat): Vec(Nat, suc(suc(zero()))) =
    cons(Nat, suc(zero()), x, cons(Nat, zero(), y, vecnil(Nat)))

  # Append: the result length is the sum, by construction.
  # vappend's implicit {A} {m} {n} are inferred from the arguments.
  proc myAppend(xs: Vec(Nat, suc(zero())), ys: Vec(Nat, suc(zero()))): Vec(Nat, add(suc(zero()), suc(zero()))) =
    vappend(xs, ys)

  # Length of a vector, by induction on the vector.
  proc vlen(A: Univ, n: Nat, v: Vec(A, n)): Nat =
    vecElim(A, lam(i, Nat, lam(w, Vec(A, i), Nat)), zero(),
            lam(i, Nat, lam(x, A, lam(xs, Vec(A, i), lam(ih, Nat, suc(ih))))),
            n, v)
```

A few notes on the syntax (the full story is in
[the surface-syntax reference](surface-syntax-reference.md)):

- `Nat` is `zero` / `suc(n)`; `suc(suc(zero()))` is the number 2.
- `cons` takes the element type and the tail length explicitly:
  `cons(A, n, x, xs) : Vec(A, suc(n))`.
- `vecnil` is the empty vector. In `.ep` files it is spelled `nil`,
  but inside `eponymBlock` — which is Nim syntax, where `nil` is a
  keyword — you write `vecnil` and the macro maps it back.
- `vecElim` is the induction principle the `data` declaration
  generates: give it a *motive* (what you are proving about every
  vector — here `lam(i, Nat, lam(w, Vec(A, i), Nat))`, "for every length
  `i` and vector `w`, produce a `Nat`"), the nil case, the cons case,
  and the vector to eliminate. The cons case gets an induction
  hypothesis `ih` for the tail.
- `{A}`, `{m}`, `{n}` in the prelude are *implicit* binders: a definition
  declares them with braces (`proc vappend {A : Type 0} {m : Nat} ...`), but you
  never write them at call sites — the elaborator fills them in.

Now ascribe a 2-element vector the type of 1-element vectors:

```nim
  proc badVec(x: Nat, y: Nat): Vec(Nat, suc(zero())) =
    cons(Nat, suc(zero()), x, cons(Nat, zero(), y, vecnil(Nat)))
```

```
vec_bad.nim(5, 3) Error: eponymBlock elaboration error: line 2, col 56:
  inferred type (Vec Nat (suc (suc zero))) does not match expected type
  (Vec Nat (suc zero)) (expected type written at line 2, col 1):
  noConfusion: distinct constructors 'suc' and 'zero' of datatype 'Nat'
  cannot be equal
```

The checker proved `2 ≠ 1` and refused the program. That is the whole
point: the length invariant is enforced where the vector is built, so
every consumer of `Vec(A, n)` can rely on it without re-checking.

## 4. Why bother: a protocol, stated once as a type

Dependent types earn their keep when the type states something a
programmer could plausibly get wrong: send before receive, use a
channel twice, drop it without closing. Here the *protocol itself* is
an indexed datatype, and the client is checked against it at compile
time.

`session.nim`:

```nim
import eponym_mac
import eponym_embed

eponymBlock:
  import "lib/nat.ep"

  # Session protocol descriptions: what comes next on the channel.
  data(Session, Univ):
    proc sendS(A: Univ, s: Session): Session
    proc recvS(A: Univ, s: Session): Session
    proc endS(): Session

  # A channel indexed by its current session state.
  data(Chan, Session -> Univ):
    proc mkChan(s: Session): Chan(s)

  # Operations as postulates (mock backend). The types enforce the
  # protocol; the linear binders enforce single use of the channel.
  postulate(sendNat, Pi(x: Nat, ch {.linear.}: Chan(sendS(Nat, endS())), Chan(endS())))
  postulate(recvNat, Pi(ch {.linear.}: Chan(recvS(Nat, endS())), Sig(x: Nat, Chan(endS()))))
  postulate(closeOp, Pi(ch {.linear.}: Chan(endS()), Nat))

  # Correct client: the channel starts as `Chan (sendS Nat endS)`;
  # the body must deliver the declared `Chan endS`.
  proc client(ch {.linear.}: Chan(sendS(Nat, endS()))): Chan(endS()) =
    sendNat(zero(), ch)

  # Server side of the dual protocol: receive a Nat, then close.
  # recvNat returns a pair; snd(p) is the continued channel.
  proc server(ch {.linear.}: Chan(recvS(Nat, endS()))): Nat =
    let p = recvNat(ch)
    closeOp(snd(p))
```

Notes:

- `data(Chan, Session -> Univ)` declares a type *indexed by* a session:
  `Chan(s)` is a different type for every protocol state `s`. The
  protocol is stated once, as data, and every operation's type says
  which state it requires and which it produces.
- `ch {.linear.}` is a quantity-1 binder: the elaborator rejects using
  a linear variable zero times or twice. Drop `ch` and you get
  `linear variable 'ch' not used (expected exactly once): a linear binder
  must be used exactly once in the body`; use it twice and you get
  `linear variable 'ch' used 2 times (expected exactly once): use the
  variable exactly once in the body`.
- Quantity inference (issue #84): you only need to *write* an annotation
  when you want quantity 1. An unannotated binder gets its quantity
  inferred from usage — zero relevant uses becomes erased (`0`), any use
  becomes unrestricted (`ω`). Linearity is never inferred, so
  `{.linear.}` (`.ep` files: `(1 x : T)`) stays required wherever you
  need it, and explicit annotations always override inference. Only
  *term* positions count as uses: a mention inside a type does not
  consume a linear variable or violate erasure.
- `postulate` declares an operation without defining it — here a mock
  backend. A real library binds these to socket code; the types are the
  contract the backend must uphold (the typed-API-over-untrusted-backend
  architecture).
- `Pi(x: Nat, ch {.linear.}: ..., ...)` is dependent function type
  syntax; `Sig(x: Nat, ...)` is a dependent pair.

Try to receive on a channel whose protocol says "send first":

```nim
  proc badClient(ch {.linear.}: Chan(sendS(Nat, endS()))): Chan(endS()) =
    let p = recvNat(ch)
    closeOp(snd(p))
```

```
session_bad.nim(5, 3) Error: eponymBlock elaboration error: line 11, col 77:
  inferred type (Chan (sendS Nat endS)) does not match expected type
  (Chan (recvS Nat endS)): noConfusion: distinct constructors 'sendS'
  and 'recvS' of datatype 'Session' cannot be equal
```

The protocol violation is a compile-time error. The same technique
scales: `examples/embedded/` has a Paxos round, a borrow checker with
unique borrows, and DCP-checked convex optimization, all as
Eponym-checked definitions used from ordinary Nim.

## 5. Where next

- [Surface-syntax reference](surface-syntax-reference.md) — every form
  the language accepts, in one place.
- [Trust model](trust-model.md) — what the checker guarantees, what is
  your problem, and the known soundness gaps. Read this before you rely
  on Eponym for anything serious.
- `examples/embedded/` — twelve complete programs mixing checked
  definitions with plain Nim: session types, the borrow checker,
  vectors, records, sensor fusion, convex optimization.
- The sheds walkthrough (`examples/embedded/sheds_walkthrough.nim`)
  for interactive, hole-driven development inside VS Code.

If something in this tutorial did not work as written, that is a bug —
please file it.
