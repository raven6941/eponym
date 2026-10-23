# Eponym surface-syntax reference

The surface grammar is one grammar: what you write in a standalone `.ep`
file and what you write inside `eponymBlock:` in Nim are the same language
(issue #144; conformance is pinned by `tests/surface_conformance.nim`, and
the Nim-side mapping for every form is pinned by
`tests/test_embedded_macro_forms.nim`). The canonical grammar lives in
`src/eponym/parse_surf.nim`:

```
decl    = proc | def | postulate | elim | red | data | record | import
          | interface | command
term    = ... Pi | Sig | lam | let | ascription | application | ?[digits] | Nat literals ...
```

Trust-model note: this document describes the syntax. What each construct
*guarantees* (and the known soundness gaps) is in `docs/trust-model.md`.

## Entering: `eponymBlock`

```nim
import eponym_mac
import eponym_embed
import elab
import eponym_init

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

### The Nim boundary

Nim syntax is the *surface notation* for Eponym declarations inside the
block; it does not make the block a normal Nim procedure body. The macro
does not evaluate arbitrary Nim expressions, resolve Nim symbols, or inline
calls to Nim libraries. It translates a supported set of Nim AST shapes to
Eponym source, then the Eponym parser and checker decide their meaning.

| Inside `eponymBlock` | Meaning |
|---|---|
| `proc f(x: T): U = term` | Eponym definition; `term` must use Eponym forms |
| `proc f[A: Univ, n: Nat, b: Bool, i: Int](x: A): Vec[A, n] = ...` | Explicit Eponym binders; `[A: Univ]` maps to an opaque Nim generic type, `[n: Nat]` and `[i: Int]` map to `static[int]`, and `[b: Bool]` maps to `static[bool]`. Binders over `runtimeType` mappings use `static[NimType]` when Nim supports that type as a compile-time value. Value binders cross through their checked runtime codec. |
| `cons[A, n](x, xs)`, `Vec[A, n]` | Square brackets supply explicit Eponym parameters; parentheses supply term arguments. Recognized call-style explicit applications are rejected with a migration diagnostic. |
| `let x = term` in a definition body | Eponym local binding; one or more lets may precede the final term |
| `left + right`, `left - right`, `left * right`, `-value` | Lowered to checked Eponym `Int` primitives; the Eponym checker enforces operand types |
| `if condition: yes elif other: maybe else: no` | Pure conditional chain lowered to nested `ifThenElse` calls from `lib/bool.ep`; import that file, use `Bool` conditions, and provide one expression per branch |
| `addInt(x, y)`, `suc(n)`, `f x`, `lam(x, T, body)` | Eponym applications and lambda forms, translated by the macro |
| `import "nat.ep"` | Eponym module import; relative to the source file first, then the installed package prelude. Absolute paths select an explicit file. |
| `bindPostulate(operation, nimProc)` | Explicit runtime binding; supported shapes are listed in [known limitations](known-limitations.md) |
| `bindPostulateMutable(operation, nimProc, ArgumentTypes..., ResultType)` | Trusted adapter that passes decoded locals to Nim `var` parameters and encodes the result; shared-reference mutation may still be visible |
| `runtimeCodec(Tree, NimType, encode, decode)` | Register typed Nim encoders/decoders for a named Eponym type or family; the codec implementation is trusted |
| `runtimeValue(checkedDefinition)` | Expose checked values and globals; imported definitions without a local Nim signature use the raw `Value` ABI |
| `requireCompiled()` | Require the representation backend and direct typed wrappers for the local and transitive imported definitions; currently limited to plain `int` mappings, with unsupported shapes rejected at compile time |
| `debugEcho[A](value)` | Opt-in runtime trace from `lib/debug.ep`; bind `debugEcho` with `debugEchoRuntimeValue` or a custom raw adapter |
| `echo`, `for`, `var`, effectful Nim control flow, Nim library calls | Not supported as host Nim statements/expressions in the block |

Put ordinary computation, IO, control flow, and Nim library calls outside
the block. Call the generated wrappers from Nim, and pass values across the
wrapper boundary using the supported runtime types. See the
[tutorial](tutorial.md) for a complete example. This is the current
boundary; a planned experiment may add a small *pure* expression subset
whose forms translate to checked Eponym terms rather than running as Nim.

Build with `-d:eponymTrustReport` to print a compile-time inventory of the
block's explicit runtime trust boundaries. It lists postulate adapters,
custom or opaque runtime mappings, and dependent-pair/record trust opt-ins,
with the guarantee each leaves to Nim. This is a human-readable build
diagnostic, not a machine-readable API.

For opaque scalar values, import `lib/float.ep` (`Float`) or `lib/text.ep`
(`String` and `Char`) and register `runtimeType` mappings to Nim's
`float64`, `string`, and `char`. The checker validates these types in
signatures and value flow. It does not provide literal syntax or built-in
operations for them; construction and operations come from Nim adapters.

### `bindPostulate` — trusted runtime adapter

```nim
proc incrementNim(value: int): int = value + 1

eponymBlock:
  postulate(Int, Univ)
  postulate(increment, Int -> Int)
  bindPostulate(increment, incrementNim)
  proc checkedRole(value: Int): Int = increment(value)

doAssert checkedRole(41) == 42
```

For this supported shape, the macro checks that the Eponym postulate is
`Int -> Int`, and Nim checks that the supplied procedure has type
`proc(int): int`. The implementation is trusted to honor its contract; Eponym
does not inspect or verify the Nim procedure body. Definitions over primitive
`Int`, `Nat`, and `Bool` generate fixed-arity Nim wrappers; `Nat` uses Nim
`int` with nonnegative runtime checks and `Bool` requires `bool.ep`. Type-level
generic binders `[A: Univ]` can use Nim generic values as opaque boxes when the
binder appears only in the checked signature. Nat binders `[n: Nat]` map to
Nim `static[int]`; Bool binders `[b: Bool]` map to `static[bool]` and require
`bool.ep`; Int binders `[i: Int]` also map to `static[int]` and cross as Eponym
integer values. All three value binder kinds can appear in checked signatures
and bodies. `runtimeValue(definition)` also emits a typed `definitionDynamic`
sibling for supported runtime-valued generic indices; it takes those indices
as ordinary Nim arguments and checks indexed values against them. A binder
over an explicitly mapped type can also use a Nim static generic value,
encoded through the mapping's runtime codec. Other Eponym
signatures need an explicit opaque mapping as shown below or one of the
supported structural codecs. Multi-argument Nim proc types with supported leaf
codecs can cross in either direction when annotated with `{.closure.}`. Calling
an explicit `proc` definition
without a supported runtime mapping fails at compile time with the missing
codec type in the diagnostic. A reachable postulate without a
binding fails when evaluated; diagnostics for missing bindings at expansion
time are not implemented.

The binding is declared once in the block and applies to checked uses there,
including imported definitions. Use sites name the postulate, while the
trusted binding remains beside its declaration for review. The generated
checked wrapper signature does not identify the Nim implementation; that
implementation is not evidence in the Eponym type.

Use `bindPostulateMutable` when an existing adapter needs `var` parameters.
It decodes arguments to mutable locals, invokes the Nim procedure,
and encodes its return value. The declared Eponym postulate still describes
the input and returned values; it does not describe mutation of the caller's
Nim variable or transfer ownership. A shallow/reference-like mapped value can
still share mutable storage with other Nim aliases, so mutation isolation is
not promised. See [known limitations](known-limitations.md#postulates-connect-checked-code-to-host-code)
for an example and the trust boundary.

Opaque Nim values can cross a checked role when the Eponym type is a named
postulate. Declare an explicit type mapping, then list the mapped Eponym types
in the postulate contract:

```nim
type ChannelHandle = object
  socketId: int

proc sendMessage(channel: ChannelHandle, message: string): ChannelHandle =
  result = channel

eponymBlock:
  postulate(Channel, Univ)
  postulate(Message, Univ)
  runtimeType(Channel, ChannelHandle)
  runtimeType(Message, string)
  postulate(send, Channel -> Message -> Channel)
  bindPostulate(send, sendMessage, Channel, Message, Channel)
  proc checkedSend(channel: Channel, message: Message): Channel =
    send(channel, message)
```

This generates a fixed-arity Nim wrapper for `checkedSend` and checks the
adapter's Nim signature. Eponym can pass the opaque boxes to the postulate,
but cannot inspect a `ChannelHandle` or prove that the Nim implementation
follows a protocol. Opaque `runtimeType` mappings must name postulated Eponym
types or indexed type families. A nullary, unindexed `data` declaration may
instead map to a Nim enum whose members use the same constructor names.
Opaque bindings support `T -> T`, `T -> U`, `T -> Nat`,
`Nat -> T -> U`, and curried contracts of arbitrary arity when every argument
and result has a runtime codec. Opaque values need explicit `runtimeType`
mappings; primitive `Int`, `Nat`, and `Bool` use their built-in codecs. The
canonical length-indexed `Vec` family can opt into its sequence codec:

```nim
eponymBlock:
  import "lib/vec.ep"
  runtimeVector(Vec)
  proc keepVector[A: Univ, n: Nat](values: Vec[A, n]): Vec[A, n] = values

doAssert keepVector[int, 3](@[2, 3, 5]) == @[2, 3, 5]
```

`Vec[A, n]` maps to `seq[A]`. The wrapper checks that input and output
sequence lengths match the declared Nat index and recursively applies the
element codec, so nested `Vec` values map to nested Nim sequences. Length
expressions support a static Nat index, `zero`, `suc`,
`add`, and `mul`. The codec requires the canonical `nil` and `cons` shape from
`lib/vec.ep`; other indexed data families need their own codecs.

The standard unindexed `List[A]` family has a matching sequence codec:

```nim
eponymBlock:
  import "lib/list.ep"
  runtimeList(List)
  proc keepList[A: Univ](values: List[A]): List[A] = values

doAssert keepList[int](@[2, 3, 5]) == @[2, 3, 5]
```

List elements use their recursive codecs, and runtime values must have the
checked `nil`/`cons` constructor shape. Other payload-bearing data families
need their own codec.

For an optional value, `runtimeOption(Option)` maps a unary Eponym family with
canonical `none` and `some` constructors to `std/options.Option`:

```nim
import std/options

eponymBlock:
  import "lib/option.ep"
  runtimeOption(Option)
  proc keepOption[A: Univ](value: Option[A]): Option[A] = value

doAssert keepOption[int](some(7)) == some(7)
doAssert keepOption[int](none(int)).isNone
```

The payload uses its recursive runtime codec. Other payload-bearing data
constructors need their own explicit codecs.

For a payload-bearing data type with a different Nim representation, define
ordinary Nim encoder and decoder procedures before the block and register them
with `runtimeCodec`. Nim checks the procedure signatures when generated
wrappers or typed postulate bindings use the codec:

```nim
import eponym_mac
import eponym_embed

proc encodeTree(value: seq[int], globals: Globals): Value = ...
proc decodeTree(value: Value, globals: Globals): seq[int] = ...

eponymBlock:
  data(Tree, Univ):
    proc emptyTree(): Tree
    proc treeNode(value: Int, tail: Tree): Tree
  runtimeCodec(Tree, seq[int], encodeTree, decodeTree)
  proc keepTree(tree: Tree): Tree = tree
```

The codec receives the checked module's `Globals`, so it can use the exact
constructor identities. Its implementation is trusted: in particular, a
codec for an indexed family must check that host values agree with the Eponym
indices. Throw `ValueError` for malformed runtime values. This escape hatch
lets libraries bridge other Nim representations without adding built-in
knowledge of each data family.

For a postulate with one to three arguments and a non-dependent pair result,
`bindPostulatePair` lets a Nim callback return a typed tuple. The macro checks
the declared argument and pair field type heads and builds the runtime pair:

```nim
postulate(split, Channel -> Sig(Nat, Channel))
bindPostulatePair(split, splitChannel, Channel, Nat, Channel)
```

The Nim callback has type `proc(ChannelHandle): tuple[int, ChannelHandle]`.
The generated codec converts the arguments and tuple recursively. Dependent
Sigma results are rejected because the host signature cannot establish the
dependent index. Indices on mapped type families remain trusted by the adapter.

When a host representation must cross a dependent pair, the trust is explicit:

```nim
postulate(Channel, Nat -> Univ)
postulate(split, Channel(0) -> Sig(index: Nat, Channel(index)))
runtimeType(Channel, ChannelHandle)
bindPostulatePairTrusted(split, splitChannel, Channel, Nat, Channel)
```

This keeps the dependent type in the checked Eponym signature, but Nim cannot
prove that the returned `ChannelHandle` represents `Channel(index)`. The host
callback must uphold that relationship. Use ordinary `bindPostulatePair` for
non-dependent results; it rejects dependent pairs.

First-order wrappers also support non-dependent `Sig(A, B)` values as
two-element Nim tuples and non-dependent named Eponym records as mapped Nim
objects. Both recursively use primitive `Int`/`Nat` codecs and explicitly
mapped opaque leaves. Record fields follow declaration order internally, while
Nim checks the named object fields and their types. Records with dependent
fields require `runtimeRecordTrusted(Record)` and a mapped Nim object. Earlier
field names feed later codecs; structural codecs can validate relationships
they represent, while any remaining index correspondence is trusted.
Dependent `Sig` values still require the separate `runtimePairTrusted`
definition opt-in.

## Sheds: `shedsBlock` (hole-driven development)

```nim
import sheds_mac
import sheds

shedsBlock:
  import "../../lib/nat.ep"

  postulate(Int, Univ)

  # Checked as usual: elaborates, gets a callable wrapper.
  proc double(x: Int): Int = addInt(x, x)

  # A shed: `![quadBody, ...]` names an unchecked scratch region whose
  # goal (here `Int`, from the ascribed return type) and context
  # (`n : Int`) are written to a sidecar file for the IDE/LSP.
  proc quad(n: Int): Int = ![ quadBody, n ++++ n ]
```

`shedsBlock:` accepts the same declarations as `eponymBlock:`; the
`![name, body]` forms are holes, not elaborated. See
`examples/embedded/sheds_walkthrough.nim` and the VS Code extension in
`editors/vscode/`.

When a refinement leaves a hole inside Nim command syntax (for example,
inside `lam f. lam g. ?`), Nim cannot parse the usual prefix marker
`![name]` in that position. The editor uses `shedHole(name)` there as a
source-level encoding of the same named shed. `shedsBlock` records and
typechecks it like `![name]`, keeping the residual goal available after
the file recompiles. Ordinary user-created sheds remain `![name]`.

## Declarations

### `data` — indexed datatypes

```nim
data(NatD, Univ):
  proc zeroD(): NatD
  proc sucD(n: NatD): NatD
```

The first argument is the index type (`Univ` = `Type 0` for unindexed types;
`Session -> Univ` for a type indexed by a session, as in
`examples/embedded/session_types.nim`). Constructors are declared with
`proc` inside the block; indices in the return type must be supplied
(`proc mkChan(s: Session): Chan(s)`). `data` desugars to
postulate/elim/red; the kernel motive-validates every generated iota rule
(see trust model). Strict positivity is checked at elaboration time (issue
#33): the type being defined may not occur in a constructor argument's
Pi-domain (negative position) or inside an index term; violations are
rejected with a located error naming the constructor and the offending
argument. The check is conservative for nested-inductive-through-indices
(see `docs/trust-model.md`).

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

`Float`, `String`, and `Char` are opaque host types, not core literals. Put
their operations in Nim and declare each operation as a postulate with a
matching `bindPostulate` adapter. The Eponym signature and the adapter's Nim
signature are checked, but the adapter's behavior is trusted; Eponym cannot
reduce a string comparison or reason about a floating-point result. This is
the v1 design boundary: it avoids making Nim's byte-string and floating-point
semantics part of Eponym's portable core. See
[known limitations](known-limitations.md#scalar-host-values-are-opaque).

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
command send : String -> 1 in Console
```

Frank-style ambient abilities threaded through `check`/`infer` at
elaboration time only — they never appear in the object program.

## Types and terms

### Universes and holes

Universes are written explicitly: `Type 0 : Type 1 : Type 2 : ...`.
`Pi`/`Sig` formation takes the maximum of the domain and codomain levels,
and `Type i` checks against `Type j` when `i <= j` at ascription points.
`Type` is contextual syntax: it parses as a universe only when followed by
an integer literal (`Type 0`, `Type 1`, …); bare `Type` remains an ordinary
identifier.

A bare `?` is a fresh hole. `?0`, `?1`, and so on name holes within one
definition: occurrences of the same number share one unknown, while different
numbers are independent. For example, `(?0, ?0)` asks for a pair with the same
unknown value in both positions; `(?0, ?1)` allows the values to differ.
`_` is a discard in binder and pattern positions, and is not a term hole.
In `eponymBlock`, `Univ` denotes `Type 0`, and Nim `_` in term position
converts to a fresh `?` hole.

### Dependent functions: `Pi`

Canonical surface (`.ep` files): one binder per `Pi`, dot before the body:

```nim
Pi {A : Type 0}. Pi (x : A). A
```

`eponymBlock` (Nim side): call syntax, the final position is the codomain:

```nim
Pi(x: Nat, ch {.linear.}: Chan(sendS(Nat, endS())), Chan(endS()))
Pi({A: Univ}, A -> A)
```

Binders are `(name : Type)`; `{name : Type}` is *implicit* — solved by
Miller-pattern unification at use sites (issue #201). Non-dependent arrows
are sugar: `A -> B` is `Pi(_ : A). B`. (The one-grammar rule means both
spellings parse the same language; the Nim side just uses call syntax
because `Pi {A : T}. body` is not valid Nim — see `tests/surface_conformance.nim`.)

### Dependent pairs: `Sig`

```nim
postulate(recvNat, Pi(ch {.linear.}: Chan(recvS(Nat, endS())), Sig(x: Nat, Chan(endS()))))
```

`Sig(x: Nat, Chan(endS()))` is the pair type; `fst(p)` / `snd(p)` project
(as in `server` in `examples/embedded/session_types.nim`).

### Lambdas: `lam`

Nim side (call syntax): `lam(x: Nat, addInt(x, x))`. Canonical surface:
`lam (x : A). x` — one binder, dot before the body, as with `Pi`.

```nim
lam(_: NatD, NatD)          # the motive in an eliminator call (Nim side)
```

### `let` (typed)

Nim side: `let p = recvNat(ch)` binds `p` in the rest of the body (as in
`server` in the tutorial). Canonical surface: `let y = x in y`.
Ascriptions work too: `(t : T)` checks `t` against `T`.

### Quantities (QTT, issues #64/#66)

Binders carry a quantity: **linear** (use exactly once), **erased** (never
used), or **unrestricted** (the default, unchecked). In `eponymBlock` the
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

**Inference (issues #84/#371).** An unannotated binder gets its quantity
inferred from usage: zero relevant uses becomes erased (`0`); exactly one
runtime use on every supported path becomes linear (`1`); other or uncertain
usage becomes unrestricted (`ω`). Path-sensitive analysis covers Nim `if`,
complete generated finite eliminators, and supported unindexed first-order
recursive eliminators with ground result motives. Known global and primitive
call signatures let the analyzer exclude type arguments and q0 arguments
from runtime use counts. An erased argument combined with a runtime use keeps
the binder unrestricted. For complete generated eliminators whose indexed or
higher-order recursion is not summarized, a value used only as the scrutinee
is still known to be consumed once; branch-dependent captures remain
conservative. Closure-valued motives, user-written eliminators, unresolved
holes, and calls without an available signature also remain conservative.
Explicit annotations always override inference. Only *term* positions count as
uses: mentions in binder domains, type annotations, and eliminator motives neither
consume a linear variable nor violate erasure. Postulates have no body to
analyze, so annotate their quantity when the API requires linear use.

### Natural numbers

Integer literals are overloaded by the expected type. In checking mode
against `Nat` they become the primitive `tNatLit` (O(1) — not a `suc`
chain); against the postulated `Int` they are primitive integers; in
inference mode a literal requires `Int` in scope. `1` in *type* position
lexes as the unit type — write `01` for the literal one (the renderer
emits `01` for `pkInt(1)` so render→parse stays faithful, issue #158).
The unit value is `<>` (Nim side: `unitv`).

`Nat` and primitive `Int` remain distinct types. To pass a natural number to
an Int-taking operation, import `lib/nat_to_int.ep` and write `natToInt(n)`.
This conversion is explicit; the elaborator does not insert it for you.

Inside `eponymBlock`, ordinary Nim integer literals can also be used for Nat
indices and bracketed arguments whose Eponym binder is `Nat`: for example,
`Vec[Nat, 2]`, `cons[Nat, 1](x, xs)`, and `vappend[Nat, 1, 1](xs, ys)`. The
macro uses the checked declaration telescope to distinguish the Nat argument
from an `Int` argument; an `Int` binder keeps Nim's literal-one spelling as
primitive `Int`. Imported prelude signatures use the same source-relative and
installed-package lookup as Eponym elaboration.

**Singleton types (issue #74).** In type position, a literal *is* its
singleton type: `(d : 2)` demands exactly `2`, Scala-3 literal-type style,
so `divBy2 : Nat -> (d : 2) -> Nat` is writable, and `divBy2 4 3` is
rejected with `inferred type 3 does not match expected type 2`. A
singleton widens to `Nat` at conversion goals — argument positions
(`divBy2 4 d` for `d : 2`), ascriptions (`(d : Nat)`), and, covariantly,
through Pi codomains and Sigma components (`proc f (d : 2) : Nat = d`
checks: the inferred `Pi(d:2).2` is accepted against the ascribed
`Pi(d:2).Nat`, mirroring the kernel's `check`, issue #223) — one
direction only (`tNatSing(k) <: Nat`; there is no narrowing). When the expected type still has unsolved metavariables
(inference-mode positions), the literal widens eagerly to `Nat` instead.

### Tactics: `by`

Canonical surface (`.ep` files): `= by refl`. Nim side: `= byTac(refl)`
(`by` is not valid Nim in that position):

```nim
proc pf1 : Eq Int 42 42 = by refl          # canonical
proc pf1(): Eq(Int, 42, 42) = byTac(refl)  # eponymBlock
proc idInt(x: Int): Int = byTac(assumption)
```

A `by <tactic>` body is discharged by an elaboration-time tactic term.
Tactic names resolve to registered tactics (`refl`, `assumption`, the
`natArithHandler` behind `by arith` for linear Nat equations, ...).
Conversion-handler effects fire at macro expansion/compile time, never in
the object program; evidence is revalidated LCF-style with handlers
uninstalled (issue #41, trust model).

### Equality

`Eq(A, x, y)` is propositional equality; `refl` proves `Eq(Int, 42, 42)`.
(#66-era core.)

## What's deliberately missing

- Termination: single-function structural recursion (#36) plus mutual
  recursion via size-change termination (#42); anything beyond that, and
  looping type-level programs in general, are the author's problem.
- Implicit-binder *lambdas* have no Nim-side spelling (parser note,
  issue #151): `{x : T}` in expression position would collide with the
  Pi-implicit table syntax, and no corpus code needs it.

## Further reading

- `docs/trust-model.md` — what the system checks vs. what is your problem.
- `docs/staging-design.md`, `docs/layers.md` — architecture (staging is
  experimental; `src/experimental/` holds code not on production paths).
- The `examples/embedded/` corpus and the compiling test corpus
  (`tests/test_embedded_macro_forms.nim`, `tests/surface_conformance.nim`)
  — every form above appears in a compiling example or test; the tutorial
  (`docs/tutorial.md`, issue #184) walks through them in order.
