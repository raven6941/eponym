# Paxos end-to-end pipeline trace (issue #355)

**Status: in progress.** Architectural checkpoint from the 2026-10-21 design
review: trace one realistic program — the checked Paxos proposer/acceptor
(#101, `examples/embedded/paxos_session.nim`) — from source through every
pipeline stage, recording every representation it becomes and every trust
boundary it crosses. Deliverables: this document, a recorded verdict on #67
(explicit IR DAG) in `decisions.org`, follow-up issues for load-bearing gaps,
and the TCB inventory below.

Sequencing: runs after the scalar (Int/Nat/Bool) fragment of #330 (landed on
main as `9373bd4`) and **gates the Vec/`seq` match-compilation work in #330**.
Not a blocker for scalar Phase 2 work, #331 design discussion, or the interop
stack.

## The program under trace

`examples/embedded/paxos_session.nim` (288 lines): dependent session types
describe the prepare/promise/accept/accepted protocol. Two checked roles:

- `proposer(ballot: Nat, ch {.linear.}: Chan(propProto())): Sig(accepted: Nat, Chan(endS()))`
- `acceptor(stored: Nat, ch {.linear.}: Chan(accProto())): Chan(endS())`

The dependent index that earns the checking: `promiseTicket(promise):
AcceptMsg(promiseValue(promise))` — the ticket type is indexed by the promised
value, so `sendAccept` can only be called with the ticket for the received
promise. Channels are linear (`{.linear.}`); `Promise`/`PaxosTicket` values
cross the runtime boundary as opaque Nim objects via explicitly trusted codecs
(`bindPostulatePairTrusted`).

## Stage 1 — Surface / embedded source (`eponymBlock`)

Modules: `src/eponym/eponym_mac.nim` (the `eponymBlock` macro),
`src/eponym/parse_surf.nim`, `src/eponym/preterm.nim`.

- [ ] What `eponymBlock` receives: Nim AST of the block; which surface forms
      the Paxos block uses (`data`, `postulate`, `runtimeType`,
      `bindPostulate`, `bindPostulatePair[Trusted]`, `proc`, `{.linear.}`).
- [ ] Surface → `PreTerm`: what is preserved, what is desugared.

## Stage 2 — Elaboration (direct elaborator)

Modules: `src/eponym/elab.nim`, `src/eponym/unify.nim` (Miller),
`src/eponym/kernel_check.nim`, `src/eponym/elab_trace.nim`.

- [ ] Where metas are created/solved while elaborating `proposer`/`acceptor`
      (implicit args, the `AcceptMsg(promiseValue(promise))` index).
- [ ] What zonking leaves behind in the elaborated `ElabDef`s.
- [ ] What `kernel_check` re-validates vs trusts.

## Stage 3 — Interactive refinement (holes/sheds)

Modules: `src/eponym/sheds.nim`, `src/eponym/sheds_mac.nim`,
`src/eponym/shed_layout.nim`, `src/eponym/lsp.nim`.

- [ ] What representation a shed actually manipulates (expected weak leg —
      record what exists, not what the UI suggests).

## Stage 4 — Erasure (#328)

Modules: `src/eponym/erasure.nim`, `src/eponym/usage_check.nim` (QTT).

- [ ] What QTT quantity information the erasure pass consumes.
- [ ] What must survive past erasure (Phase 3 / #331 linearity depends on it):
      linearity annotations on `ch`, quantity-0 proofs.
- [ ] What the erased form of the Paxos defs looks like.

## Stage 5 — The interop boundary

Modules: `src/eponym/eponym_mac.nim` (postulate/binding elaboration),
`src/eponym/eponym_init.nim` (`postulateValue`, `RuntimeBindings`),
`src/eponym/eponym_embed.nim`; `docs/trust-model.md`; #337 trust docs;
#336 var adapters; #242 arithmetic evidence.

- [ ] `runtimeType(Chan, PaxosChannel)` etc.: the codec mapping as the
      representation spec (reused by #330).
- [ ] `bindPostulate` vs `bindPostulatePair` vs `bindPostulatePairTrusted`:
      what each trusts. The Paxos ticket/index mapping is explicitly trusted.
- [ ] What crosses the boundary as opaque (`PaxosChannel`, `PaxosPromise`,
      `PaxosTicket`) and what stays checked (the indexed session types,
      linearity of the channel handle).
- [ ] Host transport (TCP in the example) — trusted, outside the checked
      fragment.

## Stage 6 — Phase 1 Value backend (#329)

Modules: `src/eponym/codegen.nim` (naive tier), `src/eponym/eponym_init.nim`
(`Value` constructors).

- [ ] What the naive backend consumes (`ElabDef`s) and preserves.
- [ ] What the emitted code for `proposer` looks like; where `Value`
      boxing remains.

## Stage 7 — Phase 2 representation backend (#330)

Modules: `src/eponym/codegen.nim` (repr tier: `reprProcs`, `compileElimProc`,
`compileDefProc`).

- [ ] Scalar fragment (landed): where `Nat`/`Int`/`Bool` stop being `Value`s
      and become host `int`s; how the typed wrapper selects the repr proc.
- [ ] Vec/`seq` (gated — not started): where host representations would
      replace `Value`s for `Vec A n`/`List`, and what the preservation
      relationship to core evaluation is at each step.
- [ ] Semantic preservation: what differential testing covers; what invariant
      would make "compiled ≡ interpreted" checkable by construction; the
      known hard corner (indexed-family match compilation) and where tests
      must target it.

## Questions the trace must answer

1. **#67 verdict:** is an explicit multi-level IR DAG needed? If yes, at
   which stage boundary does it pay for itself — and if no, what property of
   the current representations makes it unnecessary?
2. **Backend input:** what exactly should the codegen backend consume,
   long-term?
3. **Semantic preservation (Phase 2):** differential testing is necessary
   but not sufficient — see Stage 7.
4. **TCB inventory:** see below.
5. **Production pipeline membership:** does relational/staged machinery
   belong in the production pipeline, or stay experimental under the
   burden-of-proof rule (`decisions.org` 2026-10-21)?

## TCB inventory (byproduct)

From the trace, list modules/functions that are:

- (a) **trusted for soundness** —
- (b) **evidence-generating but core-validated** —
- (c) **optimization-only** —

This becomes the seed of a TCB map (cf. #242).
