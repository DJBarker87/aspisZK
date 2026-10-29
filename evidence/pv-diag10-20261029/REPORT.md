# PV_DIAG10 — D468

**Target not yet established.** Worktree exactly `/Users/dominic/ZK/.worktrees/pv-diag`, sparse branch `codex/pv-diag10-20261029`, base `2d083b9a42`. Option B, complete observer and original error bound retained. T unchanged.

## Top-down acquisition skeletons

All three compiled within the first **six** Lean attempts (66703, 66704, 66705):

- `PV_DIAG10.DIAG_FILE_TRACE`: conclusion exactly `PV_RJ4IDB.OpenInputs.DIAG_FILE_TRACE actual native`.
- `PV_DIAG10.DIAG_JSON_STDOUT_TRACE`: conclusion exactly `PV_RJ4IDB.OpenInputs.DIAG_JSON_STDOUT_TRACE actual native`.
- `PV_DIAG10.DIAG_ERROR_STDERR_TRACE`: conclusion exactly `PV_RJ4IDB.OpenInputs.DIAG_ERROR_STDERR_TRACE actual native`.

Each takes four separate standalone Props: `PV_DIAG10_Link_Init`, `PV_DIAG10_Link_Step`, `PV_DIAG10_Link_Readout`, `PV_DIAG10_Link_EventOrder`. Init fixes only the empty-prefix accumulator; Step appends only one selected event; Readout relates the real channel to its source observer state; EventOrder relates the raw ordered source events to the NativeTrace events. None mentions an OpenInputs DIAG Prop or restates the final channel equality. `prefix_agreement` proves the recurrence invariant and uses the existing native projections; no channel decoder is duplicated. The same skeleton applies to every finite prefix of a divergent execution, arbitrary index types and all terminals.

These are conditional skeletons, not deployed instances. The actual source observer's initialization, single-step updates, readout and exhaustive event-order producer remain to be associated. Instantiating state with the desired projection alone would not discharge the deployed links. Acquisition and same-public independence are distinct: panic exclusion and option-B public laws can simplify honest source-step producers but cannot by themselves establish acquisition of actual bytes.

## Focused results and remaining links

`PV_DIAG10_Observer` proves initialization and one-event accumulation for the existing decoder on translated source-model events. `*_acquisition_from_source_links` then needs only readout and event order. These are model discharges; no claim identifies the deployed observer by definition. `PV_DIAG10_Handoff.all_three_exact_inputs` combines the exact inputs; the public-channel and complete-decoder corollaries separately retain native public-event and terminal laws.

`PV_DIAG10_Attempt.attempt_from_complete_producers` derives the retry attempt-law hypothesis from `PV_DIAG10_Link_Entropy` and `PV_DIAG10_Link_MaskedAttempt`. It preserves outer termination separately from Rust Err, including Rejected and entropy errors. The latter bypasses the masked cone. Entropy panic/divergence propagate. `PV_DIAG10_Reached.reached_retry_terminates` strengthens the old criterion: only states connected by actual normal Rejected/retry edges need a complete attempt producer (`PV_DIAG10_Link_ReachedAttempt`). This is a genuine reduction of the auxiliary sufficient criterion, not removal of the deployed endpoint premise.

`PV_DIAG10_Op227.installed_family_no_panic` and `reference_family_no_panic` derive complete-invocation exclusions from the actual candidate success theorems. Installed success still uses `installed_public8 base p recipient`; `installed_nonvacuity_no_panic` remains existential in public. No theorem is silently quantified over the original arbitrary honest public input. The Bool obstruction `existential_success_not_universal` checks that invalid inference, not a native counterexample. The native public checker catches panic; `catch_return_not_panic_exclusion` checks that wrapper normal return cannot establish inner exclusion.

Exact whole-prover residuals: public-byte materialization/hash callbacks; nonce reservation and material derivation; noised-C1 clone/application and audit; domain/backend initialization and build_with_material/commitment mutation; prepare_opening; FinishContext, opening constructors, all 22 query appends, six node multiproofs/indices; ordered publish_compact; prove_from_semantics through prove_masked_attempt. Exact checker residual: public_data, emit, Lanes::new, convert, extracted_builders, ck::check plus workers/callbacks and hook/unwind behavior. op227 success removes its scoped failure only; it supplies neither whole cone. The earlier canonical compiler and encoder/capacity exclusions remain valid at their stated domains.

The Rust-panic → Result.fail .panic interpretation and applicable b3p6 body identities are **reclassification within existing Charon/Aeneas tool trust (owner fifth amendment)**. They are not new Rust semantics proofs or new T fields. Caught native panics, opaque operations and source-fidelity gaps keep their original obligations.

### Every named link

| Standalone Prop | Discharged portion | Deployed status |
|---|---|---|
| `PV_DIAG10_Link_Init` | file/json/error existing source-model observer empty state | Source association still OPEN for arbitrary actual observer |
| `PV_DIAG10_Link_Step` | file/json/error single-event decoder update, arbitrary bytes and effects | Exhaustive actual emission/read/drop/error step association OPEN |
| `PV_DIAG10_Link_Readout` | consumed by all three exact skeletons | OPEN separately for file, JSON/stdout, errors/stderr |
| `PV_DIAG10_Link_EventOrder` | all-prefix composition preserves order | OPEN for actual source events, including abnormal prefixes |
| `PV_DIAG10_Link_Entropy` | complete entropy Rust Err bypasses prover; panic/divergence propagation proved | Actual complete producer OPEN |
| `PV_DIAG10_Link_MaskedAttempt` | implies actual per-attempt law with entropy producer | Complete honest masked-attempt producer OPEN |
| `PV_DIAG10_Link_ReachedAttempt` | sufficient at reached retry states only; yields termination/panic exclusion | Actual reached producer OPEN |
| `PV_DIAG10_Link_Operands` | complete formatter, byte-length/capacity transport | Dynamic error/logger operand producer OPEN |
| `PV_DIAG10_Link_Sites` | joint call reconstructed from four fields | Honest joint occurrence/variant/site producer OPEN (original L1 obligation) |
| `PV_DIAG10_Link_Frames` | normal returned callee frames restored; earlier captures retained | Native PCs, constructor frames, workers/unwind, resolver association OPEN |
| `PV_DIAG10_Link_Levels` | public configuration can supply level, conditional on its signal binding | Actual logger binding/state OPEN |
| `PV_DIAG10_Link_Request` | adaptive off-bad history coupling proved from metadata/stopping laws | Actual request provenance OPEN |
| `PV_DIAG10_Link_WorldBlind` | sufficient byte/address/state-blind world law consumed | Deployed world law OPEN |
| `PV_DIAG10_Link_ExecutionHistory` | transports adaptive model to actual history | Actual execution/history association OPEN |
| `PV_DIAG10_Link_ChargedBad` | transfers exclusion of exactly the original headline union | Endpoint predicate association OPEN; no new bad event authorized |

### Dynamic operands, frames and V400

`PV_DIAG10_Operands` composes site, operands, live frames and level into a public invocation, then explicitly retains formatter effects and mutable logger state/replies. Normal-return stack restoration requires neither equality of previous private callee paths nor erasure of earlier captures. It is not a native-PC/unwinder theorem. The source scan rechecks 551 frozen inputs, 41 selected diagnostic sites and the inherited 463 logger candidates. plan.rs:21 formats arbitrary Debug; its selected prover-return caller has eleven unit error variants, while occurrence and variant remain joint L1 work. BlockMismatch and AuxiliaryMismatch carry dynamic coordinates and are never called OS outcomes. Configuration alone proves no logger operand law. No honest reachable witness-dependent diagnostic was constructed; provenance gaps remain OPEN, not findings.

`PV_DIAG10_Requests.request_coupling_off_bad` uses the existing adaptive replay law, retaining metadata (operation, target, offset, size, alignment, address class and retry state), replies (code, failure and partial count), stopping and every prior prefix. The context must include original public data, L1 coins/history and the retained observer prefix jointly with the option-B public world. **The adopted V400 condition is IndependentOffBad**, as clarified in LOG D262: off only the headline’s already charged union (pole/fresh-query/seed/fuel events), failure observation is witness independent. The DIAG9 all-history equalities are stronger sufficient criteria, not the definition of V400. No new event or error charge is introduced. Deployed request metadata, payload/address/allocator-written-state blindness, filesystem state, retries/Interrupted and scheduling association remain OPEN. Option B stays the single shared P row; public signal to both experiments, complete observer and bound unchanged.

### Sink disposition and endpoint accounting

All three `DIAG_*` inputs remain OPEN as deployed instances. Their exact conditional skeletons compile. Canonical compiler and named encoder model panics remain NOT REACHED under their original domain/capacity conditions; installed op227 family model panic is NOT REACHED at the named constructed public family. Whole prover, public checker, opaque callbacks, constructor/logger/backtrace effects, I/O delivery, OOM/abort/unwind/crash/register/raw-memory reporting and final visible state remain OPEN outside those scopes. Unit error names, selected literals and audit values retain inherited selected-content credit only; joint occurrence, serialization, allocation/time and delivery are retained. No channel or earlier emitted prefix is discarded.

PrivacyR1HeadlineDeployedReal.privacy_headline_deployed premises removed/added/weakened/changed: **0/0/0/0**. Before and after: actual native acquisition, original joint L1 law, deployed V400 and actual prover/checker producers are still required. V038, V178/V181, V336–V339, V347–V351 and V370 remain, with E1/E2 and D381/D386 unchanged. T is exactly entropy_law, entropy_kernel, observation. No crate/program/simulator/observer/release-pin edit, no key/account/nonce operation, merge or push.

## Verification in progress

66700 rejected: missing List.reverseRecOn; replaced with accumulator induction (66701). 66702 rejected: append notation not definitionally closed by simp only; added explicit reflexivity (66703). Neither failed source was resubmitted unchanged. Audits reserved 66797–66799. Host caps 6G/8G, swap 0, TasksMax64, Lean -M7000; one scope at a time; admission requires exit 0 and allowed:true.
