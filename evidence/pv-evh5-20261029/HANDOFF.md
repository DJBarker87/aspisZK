# D540 continuation handoff — full prover event task still unfinished

Continue ONLY in `/Users/dominic/ZK/.worktrees/pv-evh`, branch
`codex/pv-evh-20261029`. Read the prompt-pv-evh5.txt chain, pv-common.txt
(all rulings through k3, dup-1', fmt-1 and ae1), root/worktree AGENTS.md and
this directory's REPORT.md. ONLY writer; no delegation authorized. No pushes,
crates/programs changes, soundness edits, extracted-source edits or other
worktree writes. New modules use PV_EVH_. This is a CONTEXT handoff, not an
owner blocker, exhausted budget, completed task or checked counterexample.

## Receipts, IDs, host

- This resume began at `ddd4d92391`, proof work through `7cd97b6f6c` plus the
  final evidence/handoff commit. EVH5 originally resumed at `841ae0f9a9`.
- EVH4 spent 17; EVH5 now spent **37** (73623–73659 inclusive). Cumulative
  **54/100**, nominal **46 attempts remaining**, 0 native and 0 Kani.
- Next fresh ID **73660**. Audit **73699** UNUSED. Never reuse 73623–73659,
  73697/73698 or earlier consumed IDs. Leave the old admission-only skipped
  73600–73603, 73605/73606, 73613/73615 alone as already instructed. The
  nominal budget does not authorize an ID outside 73600–73699 or skipped IDs;
  only 73660–73696 and reserved 73699 remain fresh in this block.
- Read-only audit passed after 73659. `validation.json`, `host-final.json`
  and `resume-final-checks.json` reconcile all 37 EVH5 admission/out/time
  receipts, current accepted sources/objects and no live owned scope.
- FIRST git status and read-only host/receipt reconciliation before launching.
  Keep `/home/dombarker/project-offloads/codex-pv-evh-20261029` and its cache.
- New accepted modules in this resume: Prefix 73642, EntropyGenerate 73644,
  AccountCallback 73645, PrefixRetryBody 73647, PrefixLoop 73648,
  PrefixRetryRun 73649, AccountEntry 73650, MaskedAttempt 73651,
  ReserveBuild 73654, MaskedWithAttempt 73656, ReserveJoin 73657,
  ProverSpine 73658, DurableReserveBuild 73659. DO NOT rebuild or edit them
  unchanged. Earlier accepted RetryBody/RetrySource/WorldRecursion/RetryRun
  and the EVH4 substrate are retained and unchanged.
- `guard-73655.json` is an UNCHARGED pre-ID-scan/pre-submission guard refusal.
  The later actual 73655 used changed source and failed; it IS consumed.

## What is actually proved

`PV_EVH_ProverSpine.entry_fixed` is now the most composed LOCAL source Result
transport. It follows actual emitted prove_for_proof_accounts, its callback
and FnMut wrapper, retry owner, prove_masked_attempt, prove_masked_with_attempt
and reserve-and-build. No whole next/prove/with-attempt/reserve erasure law is
assumed there. The source spines are composed from named OPEN leaf executions.

It is NOT the requested complete event-producing worldRun. Account acquisition
remains a D520 input. Five head, eighteen with-attempt and eleven generic
reserve callees remain OPEN. Entropy afterDraw, nonce helper tails and
AccountEntry's op233 comparison under trait_default still contain Result-only
calls with incomplete event coverage. Allocation/drop/runtime/panic/abort,
source hash/oracle byte fidelity and actual success remain open. No full
NativeTrace projection or rtDeployed installation has been supplied.

Prefix.bind and PrefixLoop retain state/events at exhaustion separately from
source .div. All erasure claims are restricted to completed finite executions
on their named compatible dictionary domain. Preserve that distinction.

`PV_EVH_DurableReserveBuild` additionally specializes reserve-and-build to the
ACTUAL durable store instance and interprets its reservation through existing
NonceSource.reserve, lifted by Prefix.ofM. It has ten other callees OPEN and
inherits every documented nonce-helper coverage gap. It is compiled, but
NOT YET installed into the generic ProverSpine source composition.

## Exact next proof work

1. Install DurableReserveBuild in an actual-store specialized with-attempt
   source interpreter (new module, do not edit accepted generated modules).
   The existing generic ReserveJoin requires universal store/trait fields;
   avoid imposing those as actual-domain premises. Specialize the source
   header to DurableStateOnlyMaskNonceStore and the exact emitted instance,
   as open_spine.py's DurableReserveBuild does. Replace the whole reserve
   callee by the accepted specialized interpreter, carrying its ten remaining
   OPEN leaves and file Compatible domain. Then compose that actual-store
   source spine through MaskedAttempt and the account entry.
2. Replace the Result-only retry-entry op233/trait-default comparison by its
   source interpretation or an explicit named unfinished callee. Do not count
   the current Result lift as complete effect coverage. Continue expanding
   the remaining named leaf inventories in *-generation.json: allocation,
   zeroize/drop, context encode, hash/oracle, mask generation/application,
   host_semantic.build_with_material and prove_from_semantics. They are
   source-association/proof work, not a new T or an OS answer for a whole helper.
3. Close inherited Entropy.afterDraw and NonceSource reservation_path/other
   helper coverage gaps. Instantiate every reached external operation with
   its actual world state update, ordered requests/deliveries and failure,
   panic/abort/allocation paths. Preserve source restoration tuples/functions.
   Ruling fmt-1 applies to ANY reached formatting, no Unit-carrier credit.
4. Only after full coverage: complete prover worldRun and erasure on its honest
   compatible domain; prove source oraclePrefix/countTrace/nonce-fileTrace
   equal to UNCHANGED NativeTrace projections. Callees may themselves emit
   count events: never silently assume otherwise. D520 before/after/account
   inputs remain named for pv-uc, owner U/D524.
5. Only after every link is on provenance-fixed actual families and proved,
   reduce (v') consistency to successful actual worldRun nonemptiness at
   runjoin's opsNative AND allocator world. NativeObstruction62/op132 still
   blocks inferring uniform success. No unrelated MODEL VIEW earns this.
6. Focused module, dependent entry bridge, final axioms audit 73699 and one
   closure replay only when acceptance is actually ready. pv-meas's measured
   arbitrary-law event headline at `8fa34d9fb4` is unchanged and consumes the
   same links. Do not work on finite carriers or redefine native projections.

## Tools and proof pitfalls

Commit each new source first, then:

    python3 tools/pv-evh5-20261029/stage.py PV_EVH_NewModule
    python3 tools/pv-evh5-20261029/compile.py 73660 PV_EVH_NewModule

stage.py verifies the inherited SAME project/external cohort and first-root
resolution, reusing all accepted own objects. New imports outside its known
set need the inherited full prepare/cohort resolution, never a guessed object.
compile.py uses one 6G/8G/swap0/64-task scope, -M7000, same-shell admission,
cross-job ID scan, exact committed source and failed-hash guard. Admission
refusal: keep same unlaunched ID, wait FULL 180s. Pre-launch SSH reset: retain
evidence and wait 60s. Post-submission reset: recover receipts, never resubmit.
No host infrastructure changes are authorized.

All generators have --check and are checked by audit.py (read-only, no compile):
retry.py, prefix_retry.py, masked.py, open_spine.py with MaskedWithAttempt,
ReserveBuild or DurableReserveBuild, and reserve_join.py. Their original
extraction/body/source hashes and exact OPEN field signatures are retained.

open_spine.py emits per-bind FinishedView proofs and preserves source calls;
no recurrence/field arithmetic is normalized. When a source pure let introduces
an alias i, dsimp at the goal can remove it before case splitting. The final
proof tracks indented let aliases and uses `try dsimp only [aliases] at condition`
then exact branch simp. Do not repeat failed 73652/73653/73655 text. Result
carrier applications must be parenthesized (`P (alloc.vec.Vec T)`). Source
constants without argument binders need the generator's special signature path.

Do not promote the conditional local erasure structs to endpoint link proofs.
No privacy skeleton consistency credit is claimed. All endpoint/deployment
rows remain OPEN; **rows removed NONE; target not yet established**.
