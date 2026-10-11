# Eponym common library (`lib/`)

Shared Eponym definitions that would otherwise be copy-pasted into every
example (issue #114). Each module is a `.ep` file in the surface syntax.

## Using the library from an example

Add a header directive naming the module (without the `.ep` extension):

```
# import nat
```

`tests/run_examples.nim` expands the directive by prepending the module's
source before elaboration. The result is still a single standalone
elaboration unit — `#`-comments (including the directive itself) never
reach the elaborator, so no parser or elaborator changes were needed.

Directives may appear on multiple header lines; modules are prepended in
order, each at most once. Library modules may themselves carry `# import`
directives (expanded transitively).

## Modules

- **nat.ep** — `Nat` (`data` with `zero`/`suc`), `add`, `mul`.
  `add` recurses on its first argument (Idris's `plus` — `add zero n` ≡ `n`
  definitionally, which `append`'s motive relies on); `mul` is defined via
  `add`.

## Conventions

- Keep modules small and dependency-light; this is a prelude, not a
  package manager.
- Every module must elaborate standalone — `run_examples.nim` walks
  `lib/` as part of the regression suite.
- Examples that *test the mechanism itself* (e.g. `09-data-nat.ep` tests
  `data` desugaring, `08-nat-postulate.ep` tests the postulate form) stay
  self-contained and do not import.
