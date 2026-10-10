## Build-time generator for #57 (generalized fragment).
##
## Usage:
##   nim c -r --hints:off --path:src src/staging/gen_direct_elabo_full.nim \
##     > src/staging/gen_elabo_full.nim
##
## Emits gen_elabo_full.nim: the direct-style residual of the elabo/4 and
## inferoOut/4 relations (src/rel_elab_out.nim) over the FULL surface
## fragment — atoms (zero/nil/nat/univ), var, suc, app, pi, vec, lam, cons.
## No Goal/Stream machinery, no unification, no logic variables: just
## pattern matching and Option. This is the "complete staging" #26 lacked,
## generalized beyond the Vec(Nat,N) tier (gen_direct_elabo.nim).
##
## Derivation (each emitted rule cites its source clause):
##   - A `fresh` logic variable that later premises bind becomes a
##     let-binding in dependency order (app-lam: infer the argument first
##     to bind the domain, then infer the body under it).
##   - `==` against a ground term becomes a tag check + structural equality
##     (rTermEq); `==` against a manifest skeleton (vec(a,zero), pi(d,c))
##     becomes direct destructuring of the ground expected type.
##   - The host-side tag-dispatch restriction is kept: elaboD requires a
##     ground expected type, inferD a ground term. Where the relation would
##     return a non-ground answer (e.g. app(lam(b),a) with a needing an
##     expected type), the residual used to return none (#89: elaboD now
##     falls back to dynamic search via dynElabo, so ground answers found
##     by search are returned; inferD keeps the restriction).
##   - app(lam(b),a): the relation checks lam against pi(d,c) with d,c
##     free, which for ground answers is equivalent to inferring a's type
##     da and then inferring b under da (elabo(b,c) with c free degrades to
##     infer on the ground fragment — the lam/cons/nil clauses can't fire
##     without a manifest type head). So: infer a, infer b, rebuild.
##
## Branching policy (#89; Ballantyne et al. gather/fallback/later).
## Staging-time search can branch (or return non-ground answers) where the
## residual must emit a single direct-style program. Policy per site:
##   - appRedex (inferD app/lam; elaboD fallthrough): gather the
##     staging-time branches into per-branch specialized residuals; where
##     the ground reading fails (argument needs check mode, e.g.
##     app(lam,nil)), fallback to dynamic search (dynElabo) at residual
##     runtime. Staging-time enumeration of the redex's relational answers
##     shows exactly one ground branch on this fragment (elaboration of
##     ground terms is type-unique), so gather's explosion factor is 1x
##     here — the honest finding is that gather's payoff needs a fragment
##     with genuine multi-branch (e.g. overloading/coercions); fallback is
##     the policy that actually relaxes the ground-answer restriction.
##   - consIndex (elaboD cons: elabo(n, natTy())): later — residualized
##     opaquely as a recursive elaboD call, never inlined; the subgoal's
##     termination depends on runtime types.
##   - inferD (no expected type): the ground-answer restriction REMAINS —
##     fallback is unsound there since non-ground answers are
##     unrepresentable in Option[InferOut]. Documented, not implemented.
import csp

# --- CSP declarations (Issue #75): every present-stage name the residual
# --- references, with its persistence class. The generator may only emit
# --- these via lift(); the import block is derived from cspImports().
declare("natTy", "rel_elab_dep", ccHelperProc, qualified = true)
declare("zeroTm", "rel_elab_dep", ccHelperProc, qualified = true)
declare("univTy", "rel_elab_dep", ccHelperProc, qualified = true)
declare("appTm", "rel_elab_dep", ccHelperProc, qualified = true)
declare("piTy", "rel_elab_dep", ccHelperProc, qualified = true)
declare("vecTy", "rel_elab_dep", ccHelperProc, qualified = true)
declare("lamCore", "rel_elab_out", ccHelperProc, qualified = true)
declare("nilCore", "rel_elab_out", ccHelperProc, qualified = true)
declare("consCore", "rel_elab_out", ccHelperProc, qualified = true)
declare("sucCore", "rel_elab_out", ccHelperProc, qualified = true)
declare("isNatLit", "rel_elab_dep", ccHelperProc, qualified = true)
declare("rint", "minikanren", ccHelperProc, qualified = true)
declare("rpair", "minikanren", ccHelperProc, qualified = true)
declare("freshVar", "minikanren", ccEngine, qualified = true)
declare("run", "minikanren", ccEngine, qualified = true)
declare("elabo", "rel_elab_out", ccEngine, qualified = true)
declare("some", "options", ccStdlib, qualified = true)
declare("none", "options", ccStdlib, qualified = true)
declare("parseInt", "strutils", ccStdlib, qualified = true)
declare("RTerm", "minikanren", ccType, qualified = false)
declare("Option", "options", ccType, qualified = false)
declare("dec", "system", ccStdlib, qualified = false)
declare("rkAtom", "minikanren", ccType, qualified = false)
declare("rkPair", "minikanren", ccType, qualified = false)
declare("rkVar", "minikanren", ccType, qualified = false)
declare("string", "system", ccType, qualified = false)
declare("bool", "system", ccType, qualified = false)
declare("int", "system", ccType, qualified = false)

var bodyBuf = ""
proc emit(s: string) = bodyBuf.add(s & "\n")

proc genResidual*(): string =
  bodyBuf = ""
  emit ""
  emit "## Generated by staging/gen_direct_elabo_full.nim — DO NOT EDIT"
  emit "## Direct-style residual of elabo/4 + inferoOut/4 (#57, generalized)."
  emit ""
  emit "type InferOut* = tuple[ty, etm: " & lift("RTerm") & "]"
  emit ""
  emit "proc tagOfD(t: " & lift("RTerm") & "): " & lift("string") & " ="
  emit "  ## Host-side tag dispatch (cf. tagOf in rel_elab_dep)."
  emit "  if t.kind == " & lift("rkPair") & " and t.head.kind == " & lift("rkAtom") & ": t.head.name else: \"\""
  emit ""
  emit "proc rTermEq*(a, b: " & lift("RTerm") & "): " & lift("bool") & " ="
  emit "  ## Structural equality on ground RTerms (replaces `==` on ground args)."
  emit "  if a.kind != b.kind: return false"
  emit "  case a.kind"
  emit "  of " & lift("rkAtom") & ": a.name == b.name"
  emit "  of " & lift("rkVar") & ": a.id == b.id"
  emit "  of " & lift("rkPair") & ": rTermEq(a.head, b.head) and rTermEq(a.tail, b.tail)"
  emit ""
  emit "proc rTermGround*(t: " & lift("RTerm") & "): " & lift("bool") & " ="
  emit "  ## Groundness check for fallback answers (#89)."
  emit "  case t.kind"
  emit "  of " & lift("rkVar") & ": false"
  emit "  of " & lift("rkAtom") & ": true"
  emit "  of " & lift("rkPair") & ": rTermGround(t.head) and rTermGround(t.tail)"
  emit ""
  emit "proc dynElabo*(tm: " & lift("RTerm") & ", ty: " & lift("RTerm") & ", ctx: " & lift("RTerm") & "): " & lift("Option") & "[" & lift("RTerm") & "] ="
  emit "  ## #89 fallback: give up specializing; run the unstaged elabo/4"
  emit "  ## relation at residual runtime. Fires only where the specialized"
  emit "  ## (gathered) branches fail — e.g. app(lam,nil), where the argument"
  emit "  ## needs check mode and the relation's answer is found by search."
  emit "  ## Answers must be ground: the residual cannot represent non-ground"
  emit "  ## results, so a non-ground first answer degrades to none."
  emit "  let q = " & lift("freshVar") & "()"
  emit "  let sols = " & lift("run") & "(q, " & lift("elabo") & "(tm, ty, ctx, q), 1)"
  emit "  if sols.len == 0 or not rTermGround(sols[0]): " & lift("none") & "(" & lift("RTerm") & ")"
  emit "  else: " & lift("some") & "(sols[0])"
  emit ""
  emit "proc ctxLookupD*(ctx: " & lift("RTerm") & ", i: " & lift("int") & "): " & lift("Option") & "[" & lift("RTerm") & "] ="
  emit "  ## Direct reading of lookupO/3."
  emit "  var cur = ctx"
  emit "  var j = i"
  emit "  while j > 0:"
  emit "    if cur.kind != " & lift("rkPair") & ": return " & lift("none") & "(" & lift("RTerm") & ")"
  emit "    cur = cur.tail"
  emit "    " & lift("dec") & " j"
  emit "  if cur.kind != " & lift("rkPair") & ": return " & lift("none") & "(" & lift("RTerm") & ")"
  emit "  " & lift("some") & "(cur.head)"
  emit ""
  emit "proc inferD*(tm: " & lift("RTerm") & ", ctx: " & lift("RTerm") & "): " & lift("Option") & "[InferOut]"
  emit "proc elaboD*(tm: " & lift("RTerm") & ", ty: " & lift("RTerm") & ", ctx: " & lift("RTerm") & "): " & lift("Option") & "[" & lift("RTerm") & "]"
  emit ""
  # --- inferD ---------------------------------------------------------------
  emit "proc inferD*(tm: " & lift("RTerm") & ", ctx: " & lift("RTerm") & "): " & lift("Option") & "[InferOut] ="
  emit "  ## Direct reading of inferoOut/4. tm must be ground."
  emit "  if tm.kind == " & lift("rkVar") & ": return " & lift("none") & "(InferOut)"
  emit "  if tm.kind == " & lift("rkAtom") & ":"
  emit "    if " & lift("isNatLit") & "(tm):  # #87: primitive nat literal elaborates to itself, O(1)"
  emit "      return " & lift("some") & "((" & lift("natTy") & "(), tm))"
  emit "    case tm.name"
  emit "    of \"zero\": return " & lift("some") & "((" & lift("natTy") & "(), " & lift("zeroTm") & "()))     # inferoOut zero clause"
  emit "    of \"nat\": return " & lift("some") & "((" & lift("univTy") & "(), " & lift("natTy") & "()))      # type formation"
  emit "    of \"univ\": return " & lift("some") & "((" & lift("univTy") & "(), " & lift("univTy") & "()))    # type formation"
  emit "    else: return " & lift("none") & "(InferOut)                       # nil needs expected type"
  emit "  case tagOfD(tm)"
  emit "  of \"var\":  # inferoOut var clause: lookupO + etm = tm"
  emit "    let t2 = ctxLookupD(ctx, " & lift("parseInt") & "(tm.tail.head.name))"
  emit "    if t2.isNone: return " & lift("none") & "(InferOut)"
  emit "    " & lift("some") & "((t2.get, tm))"
  emit "  of \"suc\":  # inferoOut suc clause: elabo(n, nat) via check-mode call"
  emit "    let en = elaboD(tm.tail.head, " & lift("natTy") & "(), ctx)"
  emit "    if en.isNone: return " & lift("none") & "(InferOut)"
  emit "    " & lift("some") & "((" & lift("natTy") & "(), " & lift("sucCore") & "(en.get)))"
  emit "  of \"app\":  # inferoOut app clause"
  emit "    let f = tm.tail.head"
  emit "    let a = tm.tail.tail.head"
  emit "    if tagOfD(f) == \"lam\":"
  emit "      # Redex: relation elaborates lam against pi(d,c), d/c free."
  emit "      # #89 policy[appRedex]: gather — one specialized branch per"
  emit "      # staging-time branch (exactly 1 on this fragment: infer a's"
  emit "      # type, then infer the body). No fallback in infer mode: without"
  emit "      # an expected type the relation's answers may be non-ground,"
  emit "      # unrepresentable in Option[InferOut] — restriction documented."
  emit "      # Ground-fragment reading: infer a's type, then infer the body."
  emit "      let b = f.tail.head"
  emit "      let ra = inferD(a, ctx)"
  emit "      if ra.isNone: return " & lift("none") & "(InferOut)"
  emit "      let rb = inferD(b, " & lift("rpair") & "(ra.get.ty, ctx))"
  emit "      if rb.isNone: return " & lift("none") & "(InferOut)"
  emit "      " & lift("some") & "((rb.get.ty, " & lift("appTm") & "(" & lift("lamCore") & "(ra.get.ty, rb.get.etm), ra.get.etm)))"
  emit "    else:"
  emit "      let rf = inferD(f, ctx)"
  emit "      if rf.isNone: return " & lift("none") & "(InferOut)"
  emit "      if tagOfD(rf.get.ty) != \"pi\": return " & lift("none") & "(InferOut)"
  emit "      let d = rf.get.ty.tail.head"
  emit "      let c = rf.get.ty.tail.tail.head"
  emit "      let ea = elaboD(a, d, ctx)"
  emit "      if ea.isNone: return " & lift("none") & "(InferOut)"
  emit "      " & lift("some") & "((c, " & lift("appTm") & "(rf.get.etm, ea.get)))"
  emit "  of \"pi\":  # inferoOut pi clause"
  emit "    let d = tm.tail.head"
  emit "    let c = tm.tail.tail.head"
  emit "    let ed = elaboD(d, " & lift("univTy") & "(), ctx)"
  emit "    if ed.isNone: return " & lift("none") & "(InferOut)"
  emit "    let ec = elaboD(c, " & lift("univTy") & "(), " & lift("rpair") & "(ed.get, ctx))"
  emit "    if ec.isNone: return " & lift("none") & "(InferOut)"
  emit "    " & lift("some") & "((" & lift("univTy") & "(), " & lift("piTy") & "(ed.get, ec.get)))"
  emit "  of \"vec\":  # inferoOut vec clause"
  emit "    let va = tm.tail.head"
  emit "    let vn = tm.tail.tail.head"
  emit "    let ea = elaboD(va, " & lift("univTy") & "(), ctx)"
  emit "    if ea.isNone: return " & lift("none") & "(InferOut)"
  emit "    let en = elaboD(vn, " & lift("natTy") & "(), ctx)"
  emit "    if en.isNone: return " & lift("none") & "(InferOut)"
  emit "    " & lift("some") & "((" & lift("univTy") & "(), " & lift("vecTy") & "(ea.get, en.get)))"
  emit "  else:"
  emit "    " & lift("none") & "(InferOut)  # lam, cons need expected type"
  emit ""
  # --- elaboD ---------------------------------------------------------------
  emit "proc elaboD*(tm: " & lift("RTerm") & ", ty: " & lift("RTerm") & ", ctx: " & lift("RTerm") & "): " & lift("Option") & "[" & lift("RTerm") & "] ="
  emit "  ## Direct reading of elabo/4. ty must be ground (tag dispatch)."
  emit "  if tm.kind == " & lift("rkVar") & ": return " & lift("none") & "(" & lift("RTerm") & ")"
  emit "  if tm.kind == " & lift("rkAtom") & ":"
  emit "    if tm.name == \"zero\":"
  emit "      # elabo zero clause: ==(ty, nat)"
  emit "      if rTermEq(ty, " & lift("natTy") & "()): return " & lift("some") & "(" & lift("zeroTm") & "())"
  emit "      return " & lift("none") & "(" & lift("RTerm") & ")"
  emit "    if tm.name == \"nil\":"
  emit "      # elabo nil clause: ==(ty, vec(a, zero)) — reify A from ty."
  emit "      # #87: the index may be `zero` or the primitive literal 0."
  emit "      if tagOfD(ty) == \"vec\" and (rTermEq(ty.tail.tail.head, " & lift("zeroTm") & "()) or"
  emit "          rTermEq(ty.tail.tail.head, " & lift("rint") & "(0))):"
  emit "        return " & lift("some") & "(" & lift("nilCore") & "(ty.tail.head))"
  emit "      return " & lift("none") & "(" & lift("RTerm") & ")"
  emit "    # nat/univ atoms: fall through to infer-mode (type formation)"
  emit "  else:"
  emit "    case tagOfD(tm)"
  emit "    of \"lam\":"
  emit "      # elabo lam clause: ty must be manifest pi; domain reified from ty"
  emit "      if tagOfD(ty) == \"pi\":"
  emit "        let d = ty.tail.head"
  emit "        let c = ty.tail.tail.head"
  emit "        let eb = elaboD(tm.tail.head, c, " & lift("rpair") & "(d, ctx))"
  emit "        if eb.isNone: return " & lift("none") & "(" & lift("RTerm") & ")"
  emit "        return " & lift("some") & "(" & lift("lamCore") & "(d, eb.get))"
  emit "      return " & lift("none") & "(" & lift("RTerm") & ")"
  emit "    of \"cons\":"
  emit "      # elabo cons clause: ty must be manifest vec(a, suc(n))."
  emit "      # #87: the index may be a suc-chain or a primitive literal k>0"
  emit "      # whose predecessor is computed on the host — no per-node walk."
  emit "      if tagOfD(ty) == \"vec\":"
  emit "        let a = ty.tail.head"
  emit "        let nv = ty.tail.tail.head"
  emit "        var n: " & lift("RTerm") & " = nil"
  emit "        if tagOfD(nv) == \"suc\": n = nv.tail.head"
  emit "        elif " & lift("isNatLit") & "(nv):"
  emit "          let k = " & lift("parseInt") & "(nv.name)"
  emit "          if k > 0: n = " & lift("rint") & "(k - 1)"
  emit "        if n.isNil: return " & lift("none") & "(" & lift("RTerm") & ")"
  emit "        let h = tm.tail.head"
  emit "        let t = tm.tail.tail.head"
  emit "        let eh = elaboD(h, a, ctx)"
  emit "        if eh.isNone: return " & lift("none") & "(" & lift("RTerm") & ")"
  emit "        let et = elaboD(t, " & lift("vecTy") & "(a, n), ctx)"
  emit "        if et.isNone: return " & lift("none") & "(" & lift("RTerm") & ")"
  emit "        # #89 policy[consIndex]: later — the index elaboration stays an"
  emit "        # opaque recursive elaboD call; never inlined, since its"
  emit "        # termination depends on runtime types."
  emit "        let en = elaboD(n, " & lift("natTy") & "(), ctx)"
  emit "        if en.isNone: return " & lift("none") & "(" & lift("RTerm") & ")"
  emit "        return " & lift("some") & "(" & lift("consCore") & "(a, en.get, eh.get, et.get))"
  emit "      return " & lift("none") & "(" & lift("RTerm") & ")"
  emit "    else: discard"
  emit "  # fallback: infer with output, then unify the inferred type with ty."
  emit "  # #89 policy[appRedex]: gather — the specialized branch above;"
  emit "  # fallback — where it fails (e.g. app(lam,nil): the argument needs"
  emit "  # check mode), run the unstaged relation at residual runtime."
  emit "  let r = inferD(tm, ctx)"
  emit "  if r.isNone: return dynElabo(tm, ty, ctx)"
  emit "  if rTermEq(ty, r.get.ty): " & lift("some") & "(r.get.etm) else: " & lift("none") & "(" & lift("RTerm") & ")"


  # --- header: imports + CSP declarations, derived from the registry ---
  var header = ""
  for m in cspImports():
    header.add("import " & m & "\n")
  header.add("\n")
  header.add("## Generated by staging/gen_direct_elabo_full.nim — DO NOT EDIT\n")
  header.add("## Direct-style residual of elabo/4 + inferoOut/4 (#57, generalized).\n")
  header.add("##\n")
  header.add("## Cross-stage persistence declarations (Issue #75):\n")
  for r in cspRegistry:
    header.add("##   [" & $r.class & "] " & r.module & "." & r.name &
               "  (used " & $r.used & "x)\n")
  header.add("\n")
  result = header & bodyBuf

when isMainModule:
  echo genResidual()
