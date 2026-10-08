## Staging Design for Relational Engine — Track C

### Current architecture

`src/minikanren.nim` (279 lines):
- `RTerm`: var/atom/pair (ref object with case)
- `Subst`: seq[(int, RTerm)]
- `unify`: structural with occurs check
- `Stream`: explicit tree (skEmpty/skCons/skMPlus/skBind/skThunk)
- `Goal = proc(s: Subst): Stream`
- `take()`: worklist-based search
- `run()`: iterative deepening

`src/rel_elab.nim` (70 lines):
- `typeo(tm, ty, ctx)`: disj of 5 branches (zero, suc, var, lam, app)
- Each branch: `==`, `conj`, `fresh`, recursive `typeo`

### Interpretive overhead

1. **Term representation**: `RTerm` is a ref object with case dispatch.
   Every `walk`, `unify`, `$` does case analysis. For `typeo`,
   terms are S-exprs like `(suc (suc zero))` — deep nesting, many allocations.

2. **Substitution**: `seq[(int, RTerm)]`, linear lookup in `walk`.
   For deep terms, `walk` is O(depth * subst-size).

3. **Unification**: Generic structural `unify` handles all cases.
   For `typeo`, most unifications are against *known* patterns
   (e.g. `==(tm, zeroTm())` where `zeroTm()` is `ratom("zero")`).
   The generic dispatch is overhead.

4. **Stream tree**: `take()` interprets the `skMPlus`/`skBind`/`skThunk`
   tree via worklist. Each step does case analysis on StreamKind.
   The tree itself is allocated (ref objects).

5. **Goal closures**: `conj`, `disj`, `fresh` create closures.
   For `typeo`, the 5-branch `disj` creates nested closures at *construction*
   time, then `take` interprets them.

6. **Fresh variables**: `freshCounter` global, `rvar(id)` allocation per fresh.
   `typeo` uses `fresh`/`fresh2`/`fresh3`/`fresh4` — many allocations.

### Staging opportunities

**Level 1: Specialize unification for known patterns**
- `==(tm, zeroTm())` where `tm` is a var: just bind, no structural traversal
- `==(tm, sucTm(n))` where `tm` is ground: check head is "suc", bind tail
- Generate Nim code: `if tm.kind == rkAtom and tm.name == "zero": ...`
- Avoids generic `unify` dispatch

**Level 2: Specialize the relation for a query pattern**
- Query: `typeo(q, natTy(), rnil())` (synthesize Nat terms)
- The `ty` and `ctx` are *known* (static). Only `tm` is dynamic (var).
- Stage: inline the `ty==nat`, `ctx==nil` constraints
- Prune branches: `var` branch requires `ctx=(ty0 . _)`, but `ctx=nil` → fail statically
- Prune branches: `lam`/`app` produce `arr` types, but we want `nat` → fail statically
- Remaining: `zero` and `suc` branches only
- Generate: 
  ```nim
  # pseudo-code
  proc synthNat(q: RTerm, s: Subst): Stream =
    mplus(singleton(bind(q, zero)),
          bindStream(synthNatFresh(n), ...))
  ```

**Level 3: Compile the search**
- The `Stream` tree + `take` worklist is an interpreter for search.
- Stage it: generate direct Nim code with explicit stack/queue
- Inline the `mplus` interleaving as data structure operations
- Avoid `Stream` ref object allocations

**Level 4: Futamura — specialize engine for relation**
- Static: `typeo` definition (the 5 branches)
- Dynamic: query `(tm, ty, ctx)`
- Generate a *compiler* from queries to Nim code
- This is the full multi-stage miniKanren vision

### Proposed staging boundary

**Static (staging time):**
- Relation definition (`typeo` branches)
- Query pattern (which args are vars vs ground)
- Type/context constraints that prune branches

**Dynamic (run time):**
- The actual logic variables and substitutions
- Search exploration (but specialized per relation)

### Nim implementation strategy

Nim macros can do the staging:
```nim
macro stagedTypeo(tm, ty, ctx: untyped): untyped =
  # Analyze ty, ctx at compile time
  # If ty is `natTy()` literal and ctx is `rnil()`:
  #   generate only zero/suc branches
  #   inline the unifications
  # Else:
  #   fall back to interpretive typeo
```

This is *manual* staging (like `later` in the paper), not automatic.
The programmer annotates which queries to specialize.

### First concrete step

Prototype Level 2 for the specific query `typeo(q, natTy(), rnil())`:
1. Write a Nim macro `synthNat(q)` that generates the specialized code
2. Compare performance vs interpretive `run(q, typeo(q, natTy(), rnil()))`
3. Measure: time to generate first N terms

If the win is significant, generalize to a `staged` macro framework.

### Open questions

- How to handle the `Stream` tree in staged code? (Generate direct worklist code?)
- Cost model: when is staging worth it? (Aaron's spec-hash cache idea)
- Interaction with leftist heap best-first search (issue #13)?
- Can we stage the *unifier* itself for specific term shapes?

### References
- Issue #14 (this investigation)
- notes/ballantyne-multi-stage-relational-2025.org
- notes/compile-time-relational-synthesis.org
- Aaron's `research[T]` idea: compile-time search + spec-hash cache

### Update: Composition of staged relations (2026-10-07)

**Key insight:** Staged relations *compose*. 

`synthArr(q)` for `q : arr(nat,nat)`:
- Only `lam` branch viable (others pruned by ty=arr)
- Body `b : nat` in `(nat.nil)` uses `stagedWithVar(b)` 
- Result: `(lam zero)`, `(lam (suc zero))`, ... in 0.14ms

This means we don't need to stage the *entire* `typeo` at once.
We can stage *fragments* (Nat synthesis, Nat-with-var synthesis,
Arr synthesis) and compose them.

**Implications:**
- Staging scales via composition, not monolithic specialization
- Each staged fragment is small and understandable
- The macro can dispatch to pre-staged fragments based on pattern
- Full codegen (macro emits proc) works for leaf fragments;
  composition handles the recursion

**Files:**
- `src/staged_synth.nim`: synthNat (Nat, empty ctx)
- `src/staged_var.nim`: stagedWithVar (Nat, ctx=(nat.nil))
- `src/staged_arr.nim`: synthArr (arr(nat,nat), empty ctx) — composes stagedWithVar
- `src/staged_codegen.nim`: macro that *generates* (not dispatches)
- `src/staged_macro.nim`: macro with branch pruning (dispatches)
- `src/staged_rec.nim`: macro dispatching to synthNat
