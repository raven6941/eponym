# Eponym tutorial

From an installed Nim toolchain to a compile-time-checked dependent type in
about 15 minutes. Installing Nim itself is not included because the time
depends on your operating system, download speed, and toolchain choice.

Eponym is a dependently-typed language *embedded* in Nim: you write
type-checked definitions inside an `eponymBlock`, and ordinary Nim code
calls them. This tutorial takes you from installation to your first
checked dependent type to one motivating example of why dependent types
earn their keep. Every snippet below compiles as shown (each was
machine-checked while writing this document).

You will need Nim 2.2 (tested with 2.2.12 via
[choosenim](https://github.com/dom96/choosenim)) and `nimble`. Older
2.x versions may work but are untested.

## 1. Install

```sh
nimble install https://github.com/raven6941/eponym   # until the package is published
nimble install eponym        # from the nimble package directory (once published)
# or, from a checkout of this repo:
nimble install
```

This installs the elaborator modules and the Eponym prelude (`lib/*.ep`:
`Nat`, `Vec`, `Eq`, lists, …) into the nimble package directory. Set up
a project like this; the prelude directory is optional:

```
myproject/
  hello.nim
```

Relative `import "x.ep"` paths resolve first beside the Nim file containing
the block, then from the installed package's `lib/` directory. A project-local
file with the same relative path takes precedence. Use an absolute path when
you need to select a specific external `.ep` file.

## 2. Hello, checked world

`hello.nim`:

<!-- tutorial-smoke: hello -->
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
  inside checked definitions. A pure `if`/`elif`/`else` chain is translated
  into checked Eponym `ifThenElse` calls when `lib/bool.ep` is imported; it
  does not enable effectful Nim control flow. The current boundary is listed
  in the [surface-syntax reference](surface-syntax-reference.md).
- `postulate(Int, Univ)` takes `Int` as given. Universes are explicit:
  `Univ : Type 1 : ...`. In surface syntax, `_` introduces a hole to
  fill in term position (and discards a binder or pattern); named holes
  are written `?n`. The full story is in
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

A small structural codec also maps non-dependent `Sig(A, B)` values to Nim
two-element tuples. Primitive fields use the `Int`/`Nat` codecs; opaque fields
use their declared `runtimeType` mappings. For example:

```nim
eponymBlock:
  import "lib/nat.ep"
  postulate(Int, Univ)
  proc keepPair(value: Sig(Nat, Int)): Sig(Nat, Int) = value

doAssert keepPair((3, -4)) == (3, -4)
```

Named non-dependent records can also map to Nim objects with `runtimeType`;
record fields recursively use the `Int`/`Nat`, opaque, tuple, and record
codecs. Records with dependent fields require `runtimeRecordTrusted(Name)`;
earlier field names are substituted into later codecs. A Vec field checks its
length against a preceding Nat field. Any index relationship the selected
field codec cannot check remains trusted.

The standard length-indexed `Vec` family can map to Nim sequences. Opt in with
`runtimeVector(Vec)`; the wrapper checks that each sequence length agrees with
its Nat index and encodes the checked `nil`/`cons` constructors:

```nim
eponymBlock:
  import "lib/vec.ep"
  runtimeVector(Vec)
  proc keepVector[A: Univ, n: Nat](values: Vec[A, n]): Vec[A, n] = values

doAssert keepVector[int, 3](@[2, 3, 5]) == @[2, 3, 5]
```

Vector elements use their own runtime codec, including opaque Nim values
passed through a generic type parameter; nested vectors map to nested Nim
sequences. Nat length expressions support indices, `zero`, `suc`, `add`, and
`mul`.

When the length is known only at runtime, use the generated `Dynamic` sibling
instead of the `static[int]` generic wrapper. It takes the length as a Nim
`int`, keeps the vector argument as `seq[int]`, and checks their agreement
before running the checked definition:

<!-- tutorial-smoke: dynamic-vec -->
```nim
import eponym_mac
import eponym_embed

eponymBlock:
  import "lib/vec.ep"
  postulate(Int, Univ)
  runtimeVector(Vec)
  proc keepDynamicVector[n: Nat](values: Vec[Int, n]): Vec[Int, n] = values
  runtimeValue(keepDynamicVector)

let length = 3
doAssert keepDynamicVectorDynamic(length, @[2, 3, 5]) == @[2, 3, 5]
var rejectedWrongLength = false
try:
  discard keepDynamicVectorDynamic(length, @[2, 3])
except ValueError:
  rejectedWrongLength = true
doAssert rejectedWrongLength
```

A sequence whose length differs from `length` raises `ValueError` at the
runtime boundary. The raw `RuntimeValue` dynamic overload remains available
when an input type has no Nim codec.

For an unindexed collection, `runtimeList(List)` maps the standard `List[A]`
family to `seq[A]` and applies the element codec recursively:

```nim
eponymBlock:
  import "lib/list.ep"
  runtimeList(List)
  proc keepList[A: Univ](values: List[A]): List[A] = values

doAssert keepList[int](@[2, 3, 5]) == @[2, 3, 5]
```

For a direct empty-list result, write `nil` in the Nim-shaped block. Its
declared `List[...]` or `Vec[...]` type supplies the element type to the
constructor, and the runtime codec maps it to an empty Nim sequence. A typed
local works too: `let empty: List[Int] = nil`.

Now break it. Change the body to `addInt(x, y)` and recompile:

```
hello_bad.nim(5, 3) Error: eponymBlock elaboration error: line 2, col 40: unbound variable 'y'
```

Type errors inside the block are Nim compiler errors pointing at your
code — elaboration failures never crash the compiler, they are reported
like any other compile error.

## 3. Your first dependent type: length-indexed vectors

A *dependent* type is a type that mentions a value. The classic example
is vectors indexed by their length: `Vec[A, n]` is the type of vectors
with elements in `A` and length exactly `n`. It lives in the prelude —
no need to define it yourself.

`vecs.nim` (using the installed package prelude fallback):

<!-- tutorial-smoke: vecs -->
```nim
import eponym_mac
import eponym_embed

eponymBlock:
  import "lib/vec.ep"

  # A 2-vector, with its length in the type.
  proc twoNats(x: Nat, y: Nat): Vec[Nat, 2] =
    cons[Nat, 1](x, cons[Nat, 0](y, vecnil[Nat]()))

  # Generic Eponym binders and type applications use Nim's square brackets.
  proc myAppend[A: Univ, n: Nat](x: A, xs: Vec[A, n]): Vec[A, suc(n)] =
    cons[A, n](x, xs)

  # Explicitly supply the prelude's implicit binders when desired.
  proc appendTwo(xs: Vec[Nat, 1], ys: Vec[Nat, 1]): Vec[Nat, add(1, 1)] =
    vappend[Nat, 1, 1](xs, ys)

  # Length of a vector, by induction on the vector.
  proc vlen(A: Univ, n: Nat, v: Vec[A, n]): Nat =
    vecElim[A](lam(i, Nat, lam(w, Vec[A, i], Nat)), zero(),
            lam(i, Nat, lam(x, A, lam(xs, Vec[A, i], lam(ih, Nat, suc(ih))))),
            n, v)
```

A few notes on the syntax (the full story is in
[the surface-syntax reference](surface-syntax-reference.md)):

- `Nat` has constructors `zero` and `suc(n)`. In an `eponymBlock`, use
  ordinary integer literals for Nat indices and explicit Nat arguments, such
  as `Vec[Nat, 2]` and `cons[Nat, 1](...)`. The macro translates `1` to the
  Nat successor form because bare `1` in Eponym syntax is reserved for the
  unit type.
- `cons[A, n](x, xs)` takes explicit type and length parameters in brackets,
  followed by ordinary vector terms in parentheses. Call-style explicit forms
  such as `cons(A, n, x, xs)` and `Vec(A, n)` are rejected; use brackets.
- `vecnil` is the empty vector. In `.ep` files it is spelled `nil`,
  but inside `eponymBlock` — which is Nim syntax, where `nil` is a
  keyword — you write `vecnil` and the macro maps it back.
- `vecElim` is the induction principle the `data` declaration
  generates: give it a *motive* (what you are proving about every
  vector — here `lam(i, Nat, lam(w, Vec[A, i], Nat))`, "for every length
  `i` and vector `w`, produce a `Nat`"), the nil case, the cons case,
  and the vector to eliminate. The cons case gets an induction
  hypothesis `ih` for the tail.
- `{A}`, `{m}`, `{n}` in the prelude are *implicit* binders: a definition
  declares them with braces (`proc vappend {A : Univ} {m : Nat} ...`). They
  can be inferred or supplied explicitly in brackets, as in `vappend[Nat,m,n]`.

Now ascribe a 2-element vector the type of 1-element vectors:

```nim
  proc badVec(x: Nat, y: Nat): Vec[Nat, 1] =
    cons[Nat, 1](x, cons[Nat, 0](y, vecnil[Nat]()))
```

The compiler rejects `badVec`: its body has length 2, but the signature
requires length 1.

The checker proved `2 ≠ 1` and refused the program. That is the whole
point: the length invariant is enforced where the vector is built, so
every consumer of `Vec[A, n]` can rely on it without re-checking.

`Nat` and primitive `Int` are separate types. When a checked natural number
must go to an Int-taking host operation, import the explicit conversion:

```nim
eponymBlock:
  import "lib/nat_to_int.ep"
  proc countForHost(n: Nat): Int = natToInt(n)
```

The conversion is explicit so a call from `Nat` to `Int` is visible in the
checked source.

For a runtime trace from a checked definition, import `lib/debug.ep` and bind
its type-preserving postulate to the raw Value adapter. The trace runs when
the generated Nim wrapper calls the checked definition:

```nim
import eponym_mac
import eponym_embed

eponymBlock:
  postulate(Int, Univ)
  import "lib/debug.ep"
  bindPostulateValue(debugEcho, debugEchoRuntimeValue)
  proc inspect(value: Int): Int = debugEcho[Int](value)

discard inspect(42) # prints 42, then returns 42
```

The adapter is trusted Nim code and may perform IO. Eponym checks the
type-preserving call but does not model that effect.

Because `Int` is statically known at the call site, the macro generates a
typed adapter for the `debugEcho[Int]` instantiation and the compiled body
calls the host procedure directly — the `Int` witness is baked into the
adapter, so there is no per-call bindings-table lookup. A call site whose
type arguments are not statically known is a compile-time error. When the
block additionally maps `Int` to Nim `int` with `runtimeType(Int, int)`,
the macro emits a second, representation-tier adapter `proc (x: int): int`
for the instantiation — no `RuntimeValue` in its signature — and
representation-compiled definitions call it directly, with codecs only on
the adapter's value boundary.

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
- This linearity check applies to Eponym values inside the checked block.
  It cannot see whether two Nim references point to the same socket, buffer,
  or other host object. Keep aliases and ownership rules in the Nim adapter
  layer; `{.linear.}` does not make a Nim object exclusive.
- Quantity inference (issues #84/#371): an unannotated binder becomes
  erased (`0`) when unused, linear (`1`) when the checker proves exactly one
  runtime use on every supported path, and unrestricted (`ω`) otherwise.
  Path analysis covers Nim `if`, complete generated finite eliminators, and
  supported unindexed first-order recursive eliminators. Some indexed,
  higher-order, user-written, unresolved, or signature-unknown cases remain
  conservative. Write `{.linear.}` (`.ep` files: `(1 x : T)`) when the API
  contract itself must require linear use; postulates also need explicit
  quantities because they have no body to analyze. Only *term* positions
  count as uses: a mention inside a type does not consume a linear variable
  or violate erasure.
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
