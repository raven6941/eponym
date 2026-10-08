# Staging System Plan

## Vision

A small, Nim-native staging system focused on the essential operation:
**distinguish values known at different times, specialize on the known,
residualize the unknown.** AST-to-AST, no graph IR, generator runs at
compile time via Nim macros.

This is deliberately smaller than LMS. We omit:
- Runtime code generation (Nim macros cover our compile-time needs)
- Graph IR with sharing/ANF/CSE (Nim's C backend with -O2/-O3 handles it)
- Alternative compilation targets (Nim already targets C/C++/JS; via C, anything)
- Domain-specific optimization passes (the layer below us does this)

We keep:
- Binding-time distinction (`Rep[T]` / `static[T]`)
- Specialization driver (evaluate static, emit residual)
- Generic mechanism with per-language rules (tagless-final)

## Architecture

```
Layer 1 (generic):  Binding-time framework
                    - Rep[T] marker types
                    - Specialization driver
                    - Tagless-final hook (works with any Sym[R])
                    - Depends on nothing

Bridge (per-language rules):
  ETT:              - Sym[Staged] instance
                    - Rules for Pi/Sigma/lam/app/eliminators
                    - Handles metavars, conversion, dependency

  Relational:       - Relations as data (prerequisite)
                    - Mode annotations (prerequisite)
                    - Rules for fresh/==/conj/disj
                    - Mode-driven specialization

Layer 3 (clients):  Eponym elaborator, miniKanren engine, etc.
```

The mechanism is shared; the rules are per-language. This mirrors LMS
(generic core + DSL-specific staging) and our three-layer architecture
(see `docs/layers.md`).

## Key design decisions

1. **ETT core is the shared IR.** Staging operates on ETT terms via
   binding-time annotations, producing specialized ETT terms. No separate
   staging IR (avoids the `IrViewData` leakage problem).

2. **Generator = Nim macro.** Runs at compile time, emits specialized Nim
   code. Usable as a compiler: the macro is the generator, the emitted code
   is the target.

3. **Relations need restructuring first.** Current miniKanren uses closures
   (`Goal = proc(s: State): Stream`), which can't be staged by a framework.
   Prerequisite: relations as data (cf. staged-minikanren's `RelGoal` enum)
   plus mode annotations (which args are inputs vs outputs).

4. **No 2nd Futamura yet.** The framework does 1st projection (specialize
   interpreter + program → target). Self-application (`mix(mix, I)`) is
   future work; the staged-minikanren team is blocked on this and we should
   learn from their approach before attempting it.

## Phases

### Phase 0: Prototype (validate the approach)
- Hand-roll `Rep[T]` marker and one staging rule
- Apply to a tiny example (e.g., stage `evalo` for a known term manually
  through the framework, compare to hand-written `staged_eval.nim`)
- Goal: prove the framework *can* express what we do by hand

### Phase 1: Generic framework (Layer 1)
- `Rep[T]` types with binding-time propagation
- Specialization driver: walk annotated term → eval static → emit residual
- Tagless-final integration: works with existing `Sym[R]`
- Must not depend on ETT or relations

### Phase 2: ETT staging rules
- `Sym[Staged]` instance for ETT core
- Rules for each former (Pi, lam, app, eliminators, etc.)
- ETT-to-ETT passes: partial eval, let-insertion, DCE
- Handle: metavariables (defer or reject?), conversion during staging

### Phase 3: Relational staging design
- **This is a design issue, not implementation.** See GH issue.
- Decide: relations-as-data representation
- Decide: mode annotation syntax and checking
- Decide: how relational rules plug into Layer 1
- Prototype on one relation (`evalo` or `typeo`)

### Phase 4: Integration
- Stage the real Eponym elaborator (not just toys)
- Measure: correctness (same results), performance (wall-clock)
- If relational staging works, stage `typeo` for real

## Non-goals

- Replacing Nim's optimizer (we rely on it)
- Runtime/JIT staging (not our use case)
- Full LMS compatibility (we're smaller by design)
- 2nd Futamura projection (acknowledged hard; defer)

## References

- `docs/layers.md` — three-layer architecture
- abeppu/scala3-lms — general staging infrastructure (what we're *not* building)
- abeppu/staged-minikanren — relational staging (blocked on 2nd projection; learn from)
- Rompf "The Essence of Multi-Stage Evaluation in LMS" — §7 (interpreter → tagless-final)
