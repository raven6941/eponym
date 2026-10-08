# Relational Staging Design (Phase 3)

## Problem

Current miniKanren (`src/minikanren.nim`):
```nim
Goal* = proc(s: State): Stream {.closure.}
```

Goals are closures. A staging framework cannot inspect closures to derive
specialized code. This is why all our relational staging is hand-written
(`staged_eval.nim`, `staged_synth.nim`, etc.).

## Prerequisite 1: Relations as data

### Proposed `RelGoal` type

```nim
type
  RelGoalKind = enum
    rgFail, rgSucceed,
    rgEq, rgNeq,           # == and =/=
    rgConj, rgDisj,        # conjunction, disjunction
    rgFresh,               # fresh variable introduction
    rgCall,                # relation call (for recursion)
    rgSetEq,               # setEqo global constraint
    rgBranch               # branchMostConstrained (fail-first)

  RelGoal = ref object
    case kind: RelGoalKind
    of rgFail, rgSucceed: discard
    of rgEq, rgNeq: left, right: RTerm
    of rgConj, rgDisj: left, right: RelGoal
    of rgFresh: varName: string; body: RelGoal
      # Note: body is data, not a closure. The variable is named,
      # not a host-level proc parameter. This is the key shift.
    of rgCall: relName: string; args: seq[RTerm]
    of rgSetEq: cells, values: seq[RTerm]
    of rgBranch: vars: seq[RTerm]
```

### Key shift: `fresh` as data, not closure

Current:
```nim
fresh(proc(x: RTerm): Goal = ...)
```

Proposed:
```nim
RelGoal(kind: rgFresh, varName: "x", body: ...)
```

The body is a `RelGoal` value with the variable referenced by name
(`RTerm` with `rkVar` and matching name). No host closures.

### Backward compatibility

Provide `toGoal(rg: RelGoal): Goal` that interprets the data form using
the existing closure-based engine. This lets us:
1. Keep all existing code working
2. Gradually migrate relations to data form
3. Test equivalence: `run(q, toGoal(rg), n)` == `run(q, originalClosure, n)`

### What about constraints?

`=/=` and `setEqo` are already "data-like" — they take `RTerm`s and post
to stores. In `RelGoal` form:
- `rgNeq(left, right)`: posts disequality
- `rgSetEq(cells, values)`: posts set constraint
- `rgBranch(vars)`: fail-first branching over vars

These map directly to the existing `State` machinery.

## Prerequisite 2: Mode annotations

### Why modes?

Staging `evalo(tm, v)` requires knowing which arguments are inputs.
- `tm` static, `v` dynamic → evaluator (term in, value out)
- `v` static, `tm` dynamic → synthesizer (value in, term out)
- Both dynamic → full relational search (may not stage well)

### Proposed syntax

```nim
type
  Mode = enum mIn, mOut, mGround
    # mIn: must be ground at staging time (static input)
    # mOut: will be bound by the relation (dynamic output)
    # mGround: must be ground at runtime (checked, not staged)

  RelDef = object
    name: string
    params: seq[string]
    modes: seq[Mode]      # one per param
    body: RelGoal
```

Example:
```nim
RelDef(name: "evalo", params: @["tm", "v"],
       modes: @[mIn, mOut],  # tm in, v out → evaluator
       body: ...)
```

### Mode checking

Before staging, verify the mode annotation is consistent:
- `mIn` params must not be bound by the relation body (they're inputs)
- `mOut` params must be bound on all success paths (they're outputs)
- This is a simple static analysis over `RelGoal` data.

If mode check fails, refuse to stage (don't generate wrong code).

### Mode inference (issue #27)

`src/staging/modeinfer.nim` replaces the syntactic checker with
Mercury-style binding-pattern propagation over `RelGoal` data, and
derives the staging-time `dynamicVars` automatically
(`specializeRelationAuto`), removing the manual annotation at
specialization call sites.

What it does:
- Threads a bound set through the body: conjunction left-to-right,
  disjunction = intersection (bound on all success paths), `rgFresh`
  introduces a free var, `rgEq(a, b)` binds the other side's vars when
  one side is ground under the current bound set, `rgCall` records
  per-arg modes (`amIn`/`amOut`/`amMixed`) and binds the free vars of
  `mOut`-position args.
- Verifies the declared `RelDef` modes: inference reproduces
  `[mIn, mIn, mIn]` for `typeo` and `[mIn, mOut]` for `evalo`; staged
  residuals with inferred modes are byte-identical to the manual ones.
- Deliberate divergence from Mercury: an `amOut`/`amMixed` argument in a
  callee-`mIn` position is *not* an error — partial deduction handles
  any binding pattern via a per-signature specialization (this is what
  typeo's app branch needs: `typeo(a, d, ctx)` called with `d` free
  gets its own fully-dynamic specialization). It is recorded as a note.

What the user must still annotate:
- Primitive/engine relations called from `RelGoal` bodies (e.g. `addo`)
  need declared modes in `InferCtx.primModes` — inference cannot see
  through closures. An unknown callee is a hard error naming it.
- A param declared `mOut` but not bound on all success paths is a hard
  error (fix the body or weaken to `mGround`).
- `setEq`/`branch` constraints are not modeled (conservative: bind
  nothing); naked-single propagation through `setEqo` is future work.
- A "bound by body" lint notes when an `mIn` param would be bound even
  when free at call (the relation supports the output direction too).

## Framework integration (Layer 1)

### How RelGoal plugs into staging/framework.nim

The framework provides `Rep[T]`, `smartOp`, etc. For relations:

1. **Terms**: `RTerm` values can be static (ground) or dynamic (contain vars).
   Wrap as `Rep[RTerm]` where static = ground term, dynamic = term with vars.

2. **Goals**: `RelGoal` is staged by a `stageGoal(rg: RelGoal, modeEnv: ModeEnv): StagedGoal`
   where `StagedGoal` is either:
   - Fully evaluated (if all static and deterministic)
   - Residual `RelGoal` with static parts computed
   - Generated code (for `mIn`/`mOut` modes)

3. **The staging rule for each RelGoalKind**:
   - `rgEq(a, b)`: if both static RTerms, unify now (or fail). Else residualize.
   - `rgConj(a, b)`: stage a, then stage b in the resulting static env.
   - `rgDisj(a, b)`: if one branch is statically impossible, take the other.
     Else residualize the disjunction.
   - `rgFresh(name, body)`: if var only used in static positions, eliminate.
     Else introduce residual variable.
   - `rgCall(name, args)`: inline if relation is static and args match mode.
     Else residualize call.

### Connection to hand-staged versions

`staged_eval.nim` hand-writes what `stageGoal(evaloData, {tm: mIn, v: mOut})`
should derive automatically. The prototype in Phase 3 should produce
output comparable to the hand-written version.

## Open questions

1. **Search staging**: Can we stage `run` itself, or only deterministic
   forward modes? Full search staging (staging the `Stream`/`worklist`)
   is much harder. Probably limit to modes where search is not needed
   (deterministic relations with `mIn` ground).

2. **Constraint staging**: How do `=/=` and `setEqo` stage? If the constrained
   vars are static, we can check at staging time. If dynamic, residualize
   the constraint posting. The `State` stores become staging-time vs
   runtime stores.

3. **Recursion**: `rgCall` for recursive relations (like `addo`). Staging
   unrolls recursion when the decreasing argument is static. Need a
   termination check (or fuel limit) to avoid infinite unrolling.

## Deliverable

1. This design doc (done)
2. Prototype: `RelGoal` data type + `toGoal` interpreter + one staged
   relation (`evalo` with `tm` in, `v` out) producing output comparable
   to `src/staged_eval.nim`
3. Mode checker for the prototype subset

## References

- staged-minikanren `RelGoal` enum: Fail/Succeed/Fresh/Eq/Neq/Conj/Disj/Call
  (they have this working for 1st projection)
- Our `src/minikanren.nim`: closure-based `Goal` (what we're moving from)
- Our `src/staged_eval.nim`: hand-written target (what we're deriving toward)
