## Cross-stage persistence (CSP) policy for residual direct-style codegen.
##
## Issue #75. Any staged compiler must decide which present-stage values may
## be referenced from future-stage (residual) code, and how they get there
## (BER MetaOCaml's "quiet third feature" besides brackets and escape).
## This module makes the policy explicit for the #57 direct-style residual:
## every name the residual references that the residual does not itself
## define must be *declared* here with its persistence class, and the
## generator may only emit it via `lift`. The residual's import block is
## derived from the registry (`cspImports`), so the generator cannot sneak
## in undeclared dependencies.
##
## Policy per class:
##
## - ccLiteral: present-stage constants are *serialized* as literals in the
##   residual (string/int literals like "nil", "zero"). Always safe; the
##   residual never names a present-stage constant. Not registered here —
##   serialization is checked by inspection, not by the registry.
## - ccHelperProc: host helper procs (term constructors from rel_elab_dep /
##   rel_elab_out / minikanren) are *referenced by qualified name*
##   (e.g. `rel_elab_dep.natTy()`). Decision: reference, never inline. The
##   procs are trusted and total; their definitions live with the relational
##   spec, and referencing keeps a single source of truth for the encoding.
## - ccEngine: the #89 fallback needs the unstaged interpreter at residual
##   runtime (`minikanren.run`, `minikanren.freshVar`, `rel_elab_out.elabo`).
##   *Referenced by qualified name.* The residual is deliberately NOT closed
##   under this policy: dynamic search persists as a runtime dependency,
##   declared in the emitted import block.
## - ccType: type names in residual signatures (`RTerm`, `Option`) resolve
##   via declared imports; emitted unqualified (qualifying type names adds
##   noise without safety, since imports are registry-derived).
## - ccStdlib: standard-library procs (`options.some`, `options.none`,
##   `strutils.parseInt`, `system.dec`) referenced by name; qualified where
##   the module is explicit, declared where it is ambient (`system`).
##
## Invariants checked by tests/test_csp_policy.nim:
## - every declared ref is used at least once (no dead declarations);
## - the residual's import block equals the registry-derived set;
## - every occurrence of a declared qualified name in the residual is
##   spelled qualified (no bare leakage);
## - every unqualified identifier in the residual is a Nim keyword, a
##   residual-local binding, a residual-defined proc/type, or a declared
##   unqualified name.

type
  CSPClass* = enum
    ccLiteral     ## serialized into the residual; never named
    ccHelperProc  ## referenced by qualified name (term constructors)
    ccEngine      ## fallback: unstaged interpreter persists at runtime
    ccType        ## type name in signatures; resolves via declared import
    ccStdlib      ## stdlib proc; qualified where the module is explicit

  PersistentRef* = object
    name*: string
    module*: string
    class*: CSPClass
    qualified*: bool
    used*: int

var cspRegistry*: seq[PersistentRef] = @[]

proc declare*(name, module: string; class: CSPClass; qualified = true) =
  ## Declare a persistent reference the residual may use.
  cspRegistry.add PersistentRef(name: name, module: module, class: class,
                                qualified: qualified)

proc cspSpelling*(name: string): string =
  ## Residual spelling of a declared ref. Raises on undeclared names.
  for r in cspRegistry:
    if r.name == name:
      if r.qualified and r.module.len > 0:
        return r.module & "." & r.name
      return r.name
  raise newException(ValueError,
                     "CSP: undeclared cross-stage reference '" & name & "'")

proc lift*(name: string): string =
  ## Emit-spelling of a declared ref; records the use. The generator must
  ## route every residual identifier it does not define through this.
  for i in 0 ..< cspRegistry.len:
    if cspRegistry[i].name == name:
      inc cspRegistry[i].used
      return cspSpelling(name)
  raise newException(ValueError,
                     "CSP: undeclared cross-stage reference '" & name & "'")

proc cspImports*(): seq[string] =
  ## Import modules for the residual, derived from *used* refs, in
  ## first-use order. `system` is ambient and excluded.
  for r in cspRegistry:
    if r.used > 0 and r.module.len > 0 and r.module != "system" and
       r.module notin result:
      result.add r.module

proc cspUnused*(): seq[string] =
  ## Declared refs never lifted: dead declarations, fail the check.
  for r in cspRegistry:
    if r.used == 0: result.add r.name

proc cspReset*() =
  cspRegistry = @[]
