# EVH5 context handoff — full prover task still unfinished

Continue in exactly /Users/dominic/ZK/.worktrees/pv-evh on
codex/pv-evh-20261029. Read the prompt-pv-evh5.txt chain, pv-common rulings,
AGENTS.md and this directory's REPORT.md. ONLY writer. No pushes or edits to
crates/, programs/, soundness sources, other worktrees or extracted modules.
New Lean modules use PV_EVH_. No delegation was used or authorized.

## Receipt and host state

- Resume base: 841ae0f9a98c89a780803664aaf8755f48343b53.
- EVH4 spent 17; EVH5 now spent 19 (73623–73641 inclusive). Cumulative 36/100,
  leaving **64 attempts**, zero native and zero Kani. Fresh ID **73642**.
- Never reuse any of 73623–73641 or old 73697/73698. Leave prior refused IDs
  73600–73603, 73605/73606, 73613/73615 alone. Audit reserve **73699** unused.
- `validation.json` and `host-final.json` verify accepted sources/objects and
  all 19 host admission/output/time receipts. No live owned host scope remains.
  On resuming, FIRST git status and recheck host scopes/receipts before launch.
- Retain the existing host workspace/cache:
  /home/dombarker/project-offloads/codex-pv-evh-20261029.
- Four accepted new objects: RetryBody 73624, RetrySource 73636,
  WorldRecursion 73638, RetryRun 73641. Do not rebuild them unchanged.
- `python3 tools/pv-evh5-20261029/retry.py --check` reproduces RetryBody and
  its source receipt exactly. `audit.py` performs read-only receipt/source
  validation, including a host inventory; no compiler launch.

## What the new theorem really says

PV_EVH_RetryRun.run_fixed transports every FINISHED finite source retry run
under `next_fixed` and `prove_fixed` to the actual extracted retry_attempt
Result. The control spine is source-directed and contains attempt/count and
rejection events. Both `next_OPEN : Next T0` and `prove_OPEN : Prove` are still
OPEN, so this is not the full requested worldRun, and cannot remove any row.
No complete source event trace, rtDeployed binding, opsNative/allocator success
or actual-family nonemptiness was proved. D520 client inputs remain open for
pv-uc under owner U/D524. Do not claim ruling (v') completion from these local
conditional lemmas or from an unrelated model view.

## Exact next proof work, in task order

1. Instantiate next_OPEN from the actual emitted proof-account FnMut callback:
   RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError.call_mut,
   its FnMut wrapper, StateOnlyAttemptSecrets.generate_for_mask_nonce, and
   existing PV_EVH_EntropyLoop.entropyRun. The latter returns Prefix, not M.
   Introduce compositional Prefix bind (finished Result, exhausted state/events)
   or an equivalent honest finite-execution interface. NEVER turn exhaustion
   into source .div. Preserve restoration tuple t/back exactly. No opaque
   replacement of the client or whole callback trace.
2. Instantiate prove_OPEN by expanding actual prover.prove_masked_attempt,
   prover.prove_masked_with_attempt, reserve_and_build... and effectful helpers.
   Existing NonceSource and Entropy afterDraw contain Result-only lifted helpers
   that remain an event-coverage gap. The task needs all reached external ops,
   allocation/drop/runtime/panic/abort paths, not just their final Results.
   Reuse the source parser and per-bind fixed_view proofs, but keep every
   unexpanded effectful callee explicitly OPEN; do not count it as delivered.
3. Complete the extracted entry worldRun and its compatible-domain erasure;
   then prove complete prover oraclePrefix, countTrace and nonce fileTrace
   projections against UNCHANGED NativeTrace definitions. Clients before/after
   are named inputs for pv-uc. Counter projections must account for events
   emitted by all instantiated callees, not assume they cannot emit counts.
4. Only once the links are over provenance-fixed actual families and proved,
   reduce (v') consistency to successful actual worldRun existence at runjoin's
   opsNative and allocator world. Keep actual-domain nonemptiness explicit;
   NativeObstruction62/op132 prevents inferring uniform success. No extra T.
5. Focused modules first, dependent entry bridge, final axioms audit and one
   final closure replay when ready. Preserve 73699 for that audit. Existing
   73697/73698 cannot be reused. No repeated unchanged release regression.

## Commands and proof pitfalls

Commit a new module first, then:

    python3 tools/pv-evh5-20261029/stage.py PV_EVH_NewModule
    python3 tools/pv-evh5-20261029/compile.py 73642 PV_EVH_NewModule

`stage.py` verifies the SAME inherited cohort/external hashes and reuses all
accepted own modules from EVH4 and EVH5. A new import outside that known set
requires the inherited full prepare/cohort resolution, not a guessed object.
The compile wrapper uses one 6G/8G/swap0/64-task scope and -M7000, exact source
revision, admission in the same shell, cross-job ID scan and failed-hash guard.
On admission refusal keep the SAME unlaunched ID and wait full 180 seconds.
On SSH reset before launch wait 60 seconds; after submission recover receipts
and never resubmit blindly. Each refusal/transport error needs retained evidence.

Do NOT edit the four accepted modules merely to simplify their proof text.
The RetrySource failures are already solved. The pattern tuple let binders
resisted eager simplification; the final proof uses an explicit `change` of
its Continue branch before case analysis. RetryRun composes via direct state
projections s.1/s.2.1/s.2.2, avoiding anonymous tuple matchers. Increment
cases use precise bind constructor laws and final definitional equality;
no prover recurrence or field arithmetic is normalized. Prior failed source
hashes must not be recompiled unchanged.

Receipts include failed elaboration sorryAx output for diagnosis only. All
accepted theorem axioms are permitted; WorldRecursion is axiom-free. The final
report must state rows removed NONE until a genuine endpoint premise is
removed. Current stop is context handoff, not a blocker or exhausted budget.
