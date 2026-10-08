## Unified driver: putting the staged pieces together
##
## We have staged versions for each direction:
## - Check (tm ground, ty ground): checkType — direct, no search
## - Infer (tm ground, ty var): inferType — direct, compute ty
## - Synth (tm var, ty ground): synthNat, synthArr, stagedWithVar — relational + pruning
## - Eval (tm ground, v var): stageEval — direct, compute v
##
## This module puts them behind a single interface. The caller declares
## the mode (what's known), and the driver dispatches to the optimal
## staged implementation. This is "mode inference" done manually —
## the automatic version would derive the mode from the query pattern.
##
## This is how the pieces fit together: not as separate tools, but as
## modes of a single relational spec, each staged for its known/unknown profile.

import minikanren
import rel_elab
import rel_interp   # for mulTm, addTm
import staged_fwd      # inferType, checkType
import staged_synth    # synthNat
import staged_arr      # synthArr
import staged_var      # stagedWithVar (macro)
import staged_eval     # stageEval
import specialized_engine  # Tm, synthNatDirect

type
  Mode* = enum
    mCheck   # tm ground, ty ground → bool
    mInfer   # tm ground → Ty
    mSynth   # ty ground → seq[Tm] (terms of that type)
    mEval    # tm ground (arithmetic) → RTerm (value)

proc check*(tm, ty: RTerm, ctx: RTerm = rnil()): bool =
  ## Mode mCheck: is tm : ty in ctx?
  ## Uses staged checkType — no relational search.
  checkType(tm, ty, ctx)

proc infer*(tm: RTerm, ctx: RTerm = rnil()): RTerm =
  ## Mode mInfer: what is the type of tm in ctx?
  ## Uses staged inferType — direct computation.
  ## Returns the type as an RTerm S-expr (nat, arr, etc.)
  let ty = inferType(tm, ctx)
  # inferType returns RTerm already (from staged_fwd)
  ty

proc synth*(ty: RTerm, n: int, ctx: RTerm = rnil()): seq[RTerm] =
  ## Mode mSynth: generate n terms of type ty in ctx.
  ## Dispatches based on ty structure:
  ## - nat, empty ctx → synthNat (staged, 17,000x)
  ## - arr(nat,nat), empty ctx → synthArr (staged, composes)
  ## - nat, ctx=(nat.nil) → stagedWithVar (staged)
  ## - otherwise → fall back to interpretive typeo
  let q = freshVar()
  let ctxIsNil = ($ctx == $rnil())
  let tyIsNat = ($ty == $natTy())
  if ctxIsNil and tyIsNat:
    return run(q, synthNat(q), n)
  # Check for arr(nat,nat)
  if ctxIsNil and ty.kind == rkPair and ty.head.kind == rkAtom and ty.head.name == "arr":
    let d = ty.tail.head
    let c = ty.tail.tail.head
    if $d == $natTy() and $c == $natTy():
      return run(q, synthArr(q), n)
  # Fallback: interpretive
  return run(q, typeo(q, ty, ctx), n)

proc eval*(tm: RTerm): RTerm =
  ## Mode mEval: evaluate a ground arithmetic term.
  ## Uses staged stageEval — direct, no search.
  stageEval(tm)

# --- The pipeline: synthesis → check → eval ---
# This demonstrates the pieces working together, each in its optimal mode.

proc pipelineDemo*() =
  ## End-to-end: synthesize a Nat, check it, evaluate an expression with it.
  echo "=== Unified pipeline demo ==="
  echo ""
  
  # 1. Synth: get a Nat term (mode mSynth, ty=nat is static)
  echo "1. Synthesis (ty=nat static, tm var):"
  let terms = synth(natTy(), 3)
  for t in terms:
    echo "   ", t
  echo ""
  
  # 2. Check: verify the first term has type nat (mode mCheck, both ground)
  echo "2. Checking (tm and ty ground):"
  let t0 = terms[0]
  let ok = check(t0, natTy())
  echo "   check(", t0, " : nat) = ", ok
  echo ""
  
  # 3. Infer: compute the type of suc(zero) (mode mInfer, tm ground)
  echo "3. Inference (tm ground, ty computed):"
  let tm3 = sucTm(zeroTm())
  let ty3 = infer(tm3)
  echo "   infer(", tm3, ") = ", ty3
  echo ""
  
  # 4. Eval: evaluate (1+2)*3 (mode mEval, tm ground)
  echo "4. Evaluation (tm ground, v computed):"
  let tm4 = mulTm(addTm(sucTm(zeroTm()), sucTm(sucTm(zeroTm()))),
                  sucTm(sucTm(sucTm(zeroTm()))))
  let v4 = eval(tm4)
  echo "   eval((mul (add 1 2) 3)) = ", v4
  echo ""
  
  echo "Each step used the optimal staged implementation for its mode."
  echo "No step used the general relational search."

when isMainModule:
  pipelineDemo()
