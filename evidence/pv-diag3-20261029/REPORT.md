# PV_DIAG3 — D443 diagnostic execution refinement

**Target not yet established.** Native source control/ownership is refined further; the honest-run joint diagnostic law and concrete whole-client RunJoin composition remain **UNRESOLVED**. No privacy-headline premise or deployment condition is removed. No checked same-public honest-witness native diagnostic counterexample was found.

Exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-diag`; branch `codex/pv-diag3-20261029`; base `344a81b9f0`. New modules use `PV_DIAG3_`. Crates/programs, existing proofs, simulator, observer and T are unchanged. T stays `entropy_law`, `entropy_kernel`, `observation`. No wallet/key operations. See `COMMITS.txt` for the branch history.

## Native executions: what changed

The new carrier retains ordered requested and delivered bytes separately, returned-error content, captured PCs, panic metadata, allocation sizes, foreign effects and crash register/memory payloads, with final state. This is an observation specification, not a new installed observer. A crash carrier does not prove coverage of actual crash reports.

`Execution`, `Ownership` and `Reporting` distinguish normal return, panic unwind, abort and divergent finite prefixes. **Abort and divergence do not execute unwind cleanup.** On panic, cleanup retains the original panic if it returns, or invokes the explicitly supplied double-panic runtime if cleanup panics. The runtime must still be shown nonreturning and source-faithful. This corrects an overbroad feature of diag2's generic abnormal-report continuation; it is a model refinement, not a native privacy finding. Earlier effects/state are retained on every exit.

`Write` refines deployed `write_all`: empty buffer, zero write, partial write and checked slicing, Interrupted guard and destruction before retry, other errors moved to the caller. `writePrefix` has an explicit actual suffix, so finite unrolling never fabricates fuel-exhaustion divergence. `Formatter` refines the static-string fast path, mutable Adapter error replacement, successful formatting's remaining-slot destruction, moving I/O error out, and the spurious formatter-error panic. Guard/store/formatter abnormal cleanup is retained as named native work, not proved silent.

`Syswrite` binds fd2, `min(buf.len(), READ_LIMIT)`, libc write, minus-one conversion and errno reading, and the deployed integer-cast slot. OS outcomes, exact buffer/layout/cast laws and partial delivery remain P obligations. `Drop` follows anyhow's vtable to the concrete ErrorImpl Box, backtrace-before-message field order, payload-before-allocation cleanup, zero-size deallocation guard, and LazyLock's incomplete/complete/poisoned branch. LazyLock destruction does not invoke the resolver. Element drop glue, ownership/layout, allocator and destructor executions remain open.

`Capture` refines first matching symbol selection **after** the cloned frame is pushed, preserving the first selected index. Empty traces are unsupported; a missing capture-function match defaults to index zero. Status is a discriminant read, without symbolization. `createTrace` retains lock, image-base, trace callback/allocations, package/ownership and unlock operations. Native frame production, lazy resolution, filesystem/module/CWD effects and concurrent cache/lock history remain unresolved.

`source-regions.json` pins complete deployed source regions; `binding.json` checks ordered source statements and maps stores/control/drop/abort steps to model operations. These are **partial own-1 source bindings with open native operations**, not complete class-B restoration. `restored_class_B_rows` is empty. Source-to-machine preservation remains V370 at the owner's D381/D386 boundary. No machine/LLVM equality is invented.

Under own-2''' influence classification, write/errno, environment/cache, locks and unwinder/module state disqualify the affected functions from input-free treatment. Caller-confined memory primitives are permitted at V370. Allocator success/failure (rdea-1), returned addresses and later-read state writes remain explicit channels. No new singleton-domain evidence claim is made.

## Joint L1 law and client observer

`Joint.coupled_bind` transports events, related final states and the complete terminal together. `public_joint_function` consumes an **existing L1 count law** plus the separately required diagnostic law on the **same** public data and L1 simulator coin coordinates. Occurrence, emission count, selected frames, requested content and delivered content are projections of that one ordered-event equality. This is a conditional composition theorem: **`leafComposedLaw` is still required and is not established for honest native runs.** The projection lemmas are not its discharge.

Reuse D163's count/entry/erasure laws and V394's account-index disclosure. Attempt count is not a new finding. V347–V351 remain the exact producer/joint history/equal-circle/query-abort/part47 obligations; ActivePole's witness-trace dependence and rejected prefixes cannot be replaced by marginal count symmetry or a rare-event estimate.

`Client` consumes the real `ProverCommitRetry34.run` Result and retains its published count/state, terminal error variant, failure and divergence branches. `client_native_normal_model` requires the native retry Result/effect association; `client_joint_trace_transport` requires coupled native retries and coupled selected continuations. Those are unproved inputs, not an installed client instance. The source `ProverRwRetryModel.retry` law is reused and audited, not re-proved.

At the real interface, `PV_RunJoin_Deployed.rust` decodes only `execute`'s Result through `runtime.disclosed` and `runtime.observerOracle`, then `adv.decide` sees that view. `complete_observer_transport` states the sufficient Result-plus-full-prefix equality. `result_only_decoder_requires_prefix_agreement` shows the precise limitation of a Result-only decoder: if it represents two runs with the same Result, both represented prefixes must agree. It is an interface theorem, **not a native counterexample**.

The endpoint must supply:

1. Source-faithful native execution for every formatter/capture/write/lock/TLS/drop/unwind/allocator/foreign/panic/abort operation, including every emitting divergent prefix, and the concrete retry Result association.
2. One honest canonical-domain joint law on the original L1 coupling: publication/account, terminal variant and occurrence, entered/rejected prefixes, durable/oracle/entropy state, failure flag, actual frame/module selection, allocation requests and complete byte/operation trace. No independent extra diagnostic coins or new epsilon term.
3. Proof that actual `runtime.disclosed`/`observerOracle` recover every observable prefix from retained client state on all exits; then transport the resulting complete view **and decision** through V038 / `PrivacyR1HeadlineDeployedReal.RustRealRefinement`, with V036–V037 exact marginals and the existing bad/fuel event.
4. Witness-independent failure occurrence for option B (V336–V339), coherent deployment/source identity, closure replay and axioms audit. T.observation supplies native/extracted correspondence; extracted/security trace agreement remains P, never an added T field.

## Per-sink disposition

| Sink | Disposition and scope |
|---|---|
| Final Rejected report; semantic/mask mapper direct diagnostics; op227 formatting | **NOT REACHED (proved at the inherited scoped model/source paths)**. Reuse diag2's exact assumptions/exclusions and b3p6 resume7. No broader honest-run silence claim. |
| Error report after successful main Result | **NOT REACHED (proved for that arm)**; `reporting_success`. Earlier effects survive. |
| Direct retry-controller diagnostic calls | **NOT REACHED locally** by inherited structural/model binding. Actual callback/body/drop effects **UNRESOLVED**. |
| Unit prover-error spelling and exhaustion requested message | **REACHED with public-only selected content (proved conditionally on variant/normal reporting)**, inherited diag2. Variant occurrence, delivered bytes and frames **UNRESOLVED**. |
| Capture disabled branch / Backtrace status | **NOT REACHED** for create after a normally completed false enablement result, inherited diag2; status adds no symbolization by the bound discriminant body. Whole environment/capture sink **UNRESOLVED**. |
| stderr/stdout requested and delivered writes; logging; returned-error API suffix | **UNRESOLVED**: coupled native formatter/slot/lock/TLS/I/O/drop executions and honest occurrence/content law. Partial/failed writes retained. |
| Backtrace capture/resolution/frame selection | **UNRESOLVED**: callback selection rule proved, actual PC/symbol/module/CWD/cache history and allocation/drop laws required. |
| Error/message/backtrace destruction and unwind | **UNRESOLVED** globally: field/control order proved with explicit leaves; concrete destructor/allocator and failure law required. No resolver is invoked by LazyLock::drop itself. |
| Preparation and non-prover errors, ensure operands, strerror/lossy/capacity, nonce-store errors | **UNRESOLVED**: canonical-domain guard exclusion or public selected operand law, plus native execution/joint occurrence. |
| Panic, OOM, double panic, abort and foreign crash reports | **UNRESOLVED**: honest guard exclusion or joint failure/payload/size/frames/register/memory/operation law. OOM may enter the actual runtime panic/abort path; no fabricated normal exit. |

## Cohort checks, validation and stop

The retry-only imported cohort checks **922 modules, zero mismatches** (`retry-cache-preflight.json`), including recovered diag2 generation authorities. External preflight checks all **5,673** manifest objects, zero mismatches; IDs 64100–64199 have no cross-job collisions. Pinned sidecars and exact dependency objects are recorded.

The larger deployed observer closure is **not admitted**: `resume-cache-preflight.json` records 1,019 checked modules and three problems; `accepted-cache-preflight.json` records the narrower TrustItems attempt, 969 modules and the two sampler gaps. `ProverRwSampler.Funs` has two tracked variants without a proved generation/graph association; Types is reached through that unresolved module. No substitution or source overwrite occurred. `R1Z.PrivacyR1HeadlineV2`'s EJR-selected source SHA is `4321909f01b6f4d578b5e4c2198ba59406418ef8bd85f6e177f34ae107ddb694`, while the cached importer cohort records `0bb8dcc74e6d33492d386582c06836aca1ee35fc61ce898cc3afb8f6d1b20e16` (object `0cf5b991b623d35edd390a7898223015f07d28b01743aa659f06384a333ea66f`). This source/cohort mismatch blocks that composition step under h5'/h7. It is not a native witness-leak finding. The retry-only cohort is independently accepted.

Native controls use rustc **1.94.1**, opt3, debug assertions/overflow checks off, panic unwind, and the exact deployed anyhow rlib. They exercise partial/zero/failed writes, Interrupted error drop before retry, deferred returned-error destruction, Adapter errors, spurious-fmt panic, unwind drop order, anyhow drop and disabled/forced backtrace status. **Finite native validation**, not honest proving runs or universal noninterference. Binary/rlib/source/toolchain hashes are in `native-controls.json`; the deployed full Cargo-unit features/profile record is preserved in `binding.json`. The inherited client artifact is `fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348`; no rebuild or implementation change is claimed.

Final audit/resource totals are added after the final manifest receipt is collected. Stop condition is the fresh 100-attempt Lean allowance; unused native allowance is a ceiling, not a reason to launch redundant checks. Native operations, V178/V181, V347–V351, V038 and the headline refinement remain P. Before/after: no endpoint premise removed, added or reclassified as trust. The next deliverable is to prove concrete native operation instances and the honest joint leaf law, repair the named source-cohort associations without substitution, and install the complete observer transport at RunJoin.
