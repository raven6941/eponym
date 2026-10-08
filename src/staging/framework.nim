## Layer 1: Generic staging framework
##
## Provides binding-time distinction and specialization machinery usable
## by any DSL. Depends on nothing (no ETT, no relations).
##
## Design:
## - `Rep[T]`: staged value. Either static (known now) or dynamic (IR node
##   for later). The static/dynamic distinction is the essence of staging.
## - `IRNode`: base class for residual IR. DSLs extend with their own nodes.
## - `smartOp`: generic smart constructor. Folds when both args static,
##   builds IR otherwise. DSLs instantiate with their ops.
## - Tagless-final hook: any `Sym[R]` works with `R = Rep[T]`.
##
## This is the "smaller system": no graph IR, no runtime codegen, no
## optimization passes. Just binding times + specialization. The DSL
## provides the nodes; the framework provides the discipline.

type
  IRNode* = ref object of RootObj
    ## Base class for residual IR nodes. DSLs extend this with their
    ## own node types (e.g., ArithAdd, ETTApp, etc.).
    ## The framework never inspects IRNode — it's opaque residual code.
    discard

  Rep*[T] = ref object
    ## A staged value of type T.
    ## - If isStatic: value known at staging time, in staticVal.
    ## - If not: value known at runtime, represented by node (residual IR).
    isStatic*: bool
    staticVal*: T      # valid iff isStatic
    node*: IRNode      # valid iff not isStatic

proc lift*[T](x: T): Rep[T] =
  ## Lift a static value into Rep. This is the "static" injection.
  Rep[T](isStatic: true, staticVal: x)

proc dynamic*[T](node: IRNode): Rep[T] =
  ## Wrap a residual IR node as a dynamic Rep. This is the "dynamic" injection.
  Rep[T](isStatic: false, node: node)

proc getStatic*[T](r: Rep[T]): T =
  ## Extract static value. Fails if r is dynamic — this is a staging-time
  ## error (you asked for something static that isn't).
  assert r.isStatic, "getStatic: Rep is dynamic, not static"
  r.staticVal

proc smartOp*[T](a, b: Rep[T],
                 staticOp: proc(x, y: T): T,
                 mkNode: proc(x, y: Rep[T]): IRNode): Rep[T] =
  ## Generic smart constructor.
  ## - Both static → compute now (staging-time evaluation).
  ## - Otherwise → build residual IR node (defer to runtime).
  ##
  ## DSLs instantiate this with their operation and node constructor.
  ## This is the single staging rule from which others derive.
  if a.isStatic and b.isStatic:
    lift(staticOp(a.staticVal, b.staticVal))
  else:
    dynamic[T](mkNode(a, b))

proc smartOpUni*[T](a: Rep[T],
                    staticOp: proc(x: T): T,
                    mkNode: proc(x: Rep[T]): IRNode): Rep[T] =
  ## Unary version of smartOp.
  if a.isStatic:
    lift(staticOp(a.staticVal))
  else:
    dynamic[T](mkNode(a))

# --- Tagless-final hook ---
#
# Any DSL written as Sym[R] (or similar dictionary-passing style) can
# be staged by instantiating R = Rep[T]. The framework doesn't need to
# know Sym specifically — Rep[T] is just a type that DSLs can use as R.
#
# Example (see framework_test.nim):
#   type ArithSym[R] = object
#     lit: proc(n: int): R
#     add: proc(a, b: R): R
#   proc prog[R](s: ArithSym[R]): R = s.add(s.lit(1), s.lit(2))
#   prog[Rep[int]](stagedArith)  # builds IR via smartOp

when isMainModule:
  echo "Layer 1 framework loaded. See framework_test.nim for usage."
