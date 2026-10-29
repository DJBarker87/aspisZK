# PV_DIAG4 — D447 resumed diagnostic composition

Target not yet established. Branch `codex/pv-diag4-20261029`, candidate base `5a2df9074c`; exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-diag`. No implementation, observer, simulator or trust-list edits; no wallet/key operations.

## Stage 1: fresh EJR V2 replay

The authority remains EJR blob `431494fb8678733178af8c5c58cb18fbcb49f3b9`, source SHA256 `4321909f01b6f4d578b5e4c2198ba59406418ef8bd85f6e177f34ae107ddb694`. Rejected historical cached source `0bb8dcc74e6d33492d386582c06836aca1ee35fc61ce898cc3afb8f6d1b20e16`, object `0cf5b991b623d35edd390a7898223015f07d28b01743aa659f06384a333ea66f`. No substitution.

Attempt 64500 failed because this job initially omitted a private `.olean.server` link; this was an input preparation error, corrected by pinning sidecars. Attempt 64501 freshly elaborates the exact EJR source with 730 recursively hash-checked dependencies and all 5,673 external objects checked. It exits 1 at line 100: **`No goals to be solved`** (`rfl` after `simp only`). Full output, exact source snapshot, dependencies, revision, wall/RSS/swap and axioms appear in the raw receipt. This is an authoritative-source/cohort replay finding, not a native witness-leak finding. The source is not edited.

`cohort-plan.json` lists the eleven affected modules in dependency order. Only `R1Z.PrivacyR1HeadlineV2` was attempted; no successful object was admitted. Its ten downstream consumers are blocked by that predecessor and were not compiled against the rejected cached variant. Thus no unchanged-consumer missing-declaration finding is claimed. The endpoint rebuild is incomplete for the exact recorded reason.

## Stage 2: recovered sampler cohort

`sampler-generation-chain.json` checks h7 in order. The import-union graph has neither sampler module. Original translation audit pins LLBC `d1c0de02449c6f9fd2b7f436e83f7e4684c4ee57edd00735fefbb41d46293bb8`, emitted Funs `9b6819ebad4b003c45596b1b9447f9dce332bd769daeaf2e04197da61df8ef5c`, Types `a3e9e1b589c3ae6ededd2d6703c57c5929738676d4f63824cb86b930f97f417a`, and translation JSON. The committed normalization record gives exactly one historical replacement `32#i32` → `32#u32`, producing tracked Funs `212c9ad85b39125c974e014daf6c679daccaf89c56719fe7d500249efd209ae5`. This adaptation is disclosed; the tracked file is **not** described as unmodified extractor output.

Input/source snapshots and accepted receipts 11200,11202,11205 tie that result to the unchanged `ProverRwSamplerArithmetic` source `53cdde9e39c99bb4f37550854f9ba35c93f38802467159d5f8067015ff6eb57a`. The historical environment audit pins its sampler object `6447b58728cca2fa5e436978e27ed5eed84a4b14e29ed14d6cf6bc69640641cf` and dependency graph. This satisfies h7(2); STEP 4 is unnecessary. No extractor was run or changed, and no new deployed-extraction fidelity credit is claimed from historical generation recovery.

**Types, Funs and all 24 affected downstream consumers independently reachable without V2 freshly elaborate unedited**: 64502–64524,64538–64540. The precise list, source/object hashes and current direct dependency hashes are in `rebuilt-modules.json`. The final dependent module `PV_RunJoin_Deployed` is blocked by V2. The 959/962-module preparation audits checked source authority and recorded dependency fingerprints. `final-pre.json` checks the actual **998-object** current loading closure with **zero mismatches**, including new object hashes; a same-source cache is not reused across a changed dependency fingerprint. No shared source/object or another job's directory was overwritten.

## Concrete leaves and limits

New modules use `PV_DIAG4_`. `leaf-bindings.json` pins 17 complete deployed 1.94.1 source regions, statement/control/ownership mappings, native controls and source hashes. The libc EINTR constant is taken from **stdlib's own lockfile** (0.2.178), checked against the cached crate archive's Cargo checksum and exact member bytes. It is not guessed from the application's newer libc version. Source-to-machine preservation remains **V370 / pending D381/D386**. No machine/LLVM equality is assumed.

* `Leaves`: Backtrace::status borrows only the discriminant, without forcing or dropping captured frames; raw Stderr new/vectored/flush return their literal results; panic_output constructs Some(Stderr). These bodies have no opaque callee after the bound constructor. The laws concern diagnostic emissions, not complete machine timing.
* `Once`: the exclusive Linux futex state load selects 3=incomplete,2=poisoned,0=complete. Poisoned LazyLock drop has no field destruction and adds no unwind effect. Incomplete/complete keep the selected destructor. Invalid words retain the actual invalid-state panic obligation, never an invented silent branch.
* `ReprDrop`, `Bits`: prove OS-word tag/nonzero/bound/high-word and signed32 bit-pattern/Interrupted arithmetic. Noncustom valid io::Error representations drop only scalars/static references; custom Box/trait/allocator destruction is retained. Arbitrary unsafe pointer/provenance/enum validity is not discharged by the abstract valid-representation carrier.
* `Interrupted`, `RawWrite`: instantiate the raw stderr error guard and OS/WriteZero destruction slots in the inherited write_all model. An Interrupted OS error resumes the **same buffer and actual suffix**, retaining the write's complete prior events. Noninterrupted errors move to the caller. The Linux read limit is ssize_t::MAX (2^63−1), and the integer cast is explicitly modulo 2^64. Syscall outcomes, partial delivery, slice panic, locks/TLS and their joint law remain P.
* `Errno`: last_os_error follows the **foreign errno_location execution**, then loads its returned pointer's state and constructs the OS error. Normal, panic, abort and divergent prefixes are retained. There is no blanket purity law for the foreign call; valid native pointer/memory association remains explicit.

Native controls are **finite validation**, not honest proving runs, singleton-domain evidence or a universal native privacy proof. Final controls native11/native12 pin their exact source/binary inputs and exercise disabled/captured status, OS/simple/custom error drop, stored errno/Interrupted, and incomplete/complete/poisoned LazyLock destruction under rustc1.94.1,opt3,debug/overflow checks off,panic unwind. Earlier exploratory controls are retained, not promoted to stronger evidence. The final source-binding scope is native13. The harness uses std only; the deployed full application feature/profile inventory and artifact `fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348` are inherited, not rebuilt.

## Honest L1 law and observer composition

`LeafTrace.concrete_leaves_exact` proves every finite sequence of the selected silent leaves emits **zero diagnostic events**, preserves state, and retains all leaf return values. `silent_leaves_emission_joint` reuses an existing L1 count equality to prove the diagnostics-only joint projection `(count,[])`. Its diagnostic-law premise is genuinely discharged for these leaves. `silent_leaves_return_control_retained` shows the caller receives status/Interrupted results; it cannot silently erase branches controlled by them.

This is **not** the honest joint law for the whole native client. It neither covers all capture/frame production nor equates the selected continuation, returned variant, errno/I/O outcome, allocator failure or timing. Existing D163 count laws and V394 account-index disclosure are reused, not re-proved. V347–V351 still own entered/rejected prefixes, ActivePole witness-trace dependence, publication/history and the common L1 coupling. No fresh diagnostic coins, epsilon term, experiment change or public-failure assumption was added.

The real endpoint still must supply native retry Result/effect association; complete leaf/formatter/capture/drop/unwind/write/foreign executions on every exit and emitting divergent prefix; one honest joint trace law with public data and the original L1 simulator coins; witness-independent option-B failure (V336–V339); and concrete disclosed/observerOracle recovery of all observable prefixes and observer decision for V038 with V036–V037 exact marginals. The Result-only interface does not provide the missing prefix law. The deployed endpoint cannot currently replay because of the fresh V2 failure. No replacement endpoint is installed.

## Per-sink dispositions

All inherited proofs retain their original scoped assumptions; their prior universal obligations are not upgraded. The mechanical corpus is still a conservative inventory, not an established complete linked/foreign/crash-effect enumeration.

| Sink / precursor | Disposition and exact remaining obligation |
|---|---|
| main successful stdout JSON, account/count/audit/protocol/timing | **UNRESOLVED** whole public joint law and actual serialization/write delivery; V394 count disclosure is already public. |
| Final Rejected report/tag | **NOT REACHED (inherited scoped proof)** under the concrete retry Result association/RejectFree; earlier attempt effects survive. |
| Local semantic/mask mapper diagnostics; direct retry-controller diagnostics | **NOT REACHED locally (inherited scoped proof/binding)**; callback/body/drop/timing effects remain **UNRESOLVED**. |
| Selected eleven unit prover-error spellings and exhaustion requested text | **REACHED with public-only selected content (inherited conditional proof)**; honest variant/occurrence, capture and delivery remain **UNRESOLVED**. |
| Report after successful main Result | **NOT REACHED in that arm (proved)**; no claim about earlier effects or universal success. |
| plan::err → anyhow → Termination → stderr / returned API suffix | **UNRESOLVED**: concrete formatter/capture/slot/lock/TLS/write/drop/unwind and honest joint occurrence/content law. |
| Client explicit ensure/anyhow guards, non-prover/preparation errors, fancy ensure render | **UNRESOLVED**: canonical-domain guard exclusion or public selected operands/lengths, with complete native execution and joint occurrence. |
| Nonce-store returned errors / last_error state | **UNRESOLVED**: reservation/OS/history/failure public joint law. No files/keys/nonce state were created. |
| _print/_eprint/print_to, dependency logging and logger dispatch | **UNRESOLVED**: level/environment/logger/TLS/lock/format/write/failure effects and complete reached-cone coverage. |
| Raw stderr metadata/flush/panic_output constructor | **NOT REACHED for diagnostic emission in these complete leaf bodies (proved under source binding)**. panic_output does not execute the panic hook or write. Public outer locked flush remains separate. |
| Raw write_all Interrupted OS-error guard/destruction | **NOT REACHED for extra guard/drop diagnostics (proved on valid OS representation)**. The real syscall's earlier effects and selected retry suffix are retained; complete I/O and failure joint law **UNRESOLVED**. |
| Backtrace status | **NOT REACHED for capture/symbolization/emission by this accessor (proved)**; selected status may control later formatting. |
| Backtrace enablement/disabled branch | **NOT REACHED for create after normal false enablement (inherited proof)**; native environment/cache/concurrency and actual constructor occurrence remain **UNRESOLVED**. |
| Backtrace capture, actual PC/frame selection and symbolization | **UNRESOLVED**: raw unwinder frames, image/module/CWD/cache/lock/allocations, selected frame count/order, resolution and emitted bytes on the same L1 history. |
| LazyLock poisoned destruction | **NOT REACHED for field/resolver execution in that branch (proved)**. Earlier poisoning/panic is retained. Incomplete/complete field drops, anyhow/Vec/Box destruction and general unwind **UNRESOLVED** globally. |
| Noncustom valid io::Error destruction | **NOT REACHED for payload destructor diagnostics in that branch (proved)**; custom payload/Box/allocator and native unsafe representation relation retained. |
| strerror, UTF-8-lossy, estimated_capacity and ensure buffer lengths | **UNRESOLVED** selected operands, call occurrence, allocation requests and eventual emitted bytes. These are precursors, not automatically emissions. |
| op227 formatting | **NOT REACHED on the inherited scoped honest path** (b3p6 resume7); other panic sites unaffected. |
| General panic/default hook, OOM, double panic and abort | **UNRESOLVED** honest guard exclusion or joint payload/size/frame/failure/operation law. Abort/divergence do not run unwind cleanup; no fabricated return. |
| Foreign writes, fatal signals and crash reports | **UNRESOLVED** configured reporter/reached-effect closure and joint bytes/PCs/registers/memory/payload law. |

No checked same-public honest-witness native diagnostic leak was found. The V2 finding is a formal replay/cohort obstruction, not a native leak finding.

## Verification status

**46/100 Lean attempts**, IDs 64500–64542 and 64597–64599; **15/40 native scopes**, **0 Kani**. Every admitted launch has exit0 and allowed:true in the launching wrapper. One reservation refusal and two own-input prelaunch failures are separately recorded; no VOID or cooldown slip is credited. Total GNU-time wall **86.29s**, peak RSS **4,308,848KiB**, all swaps **0**. `attempts.json` retains exact targets/commands, source/dependency hashes, resource receipts, baseline revision labels and complete output.

| Audit ID | Exact target | Exit | GNU wall | Peak RSS KiB | Swap | Source revision |
|---|---|---:|---:|---:|---:|---|
| 64597 | `PV_DIAG4_Audit` | 0 | 0:02.21 | 4269596 | 0 | `b92d9aa056a97686a6ff3027bdbe09216d82edbc` |
| 64598 | `PV_DIAG4_CohortAudit` | 0 | 0:02.07 | 4268748 | 0 | `b92d9aa056a97686a6ff3027bdbe09216d82edbc` |
| 64599 | `PV_DIAG4_FinalManifest` | 0 | 0:01.83 | 4278084 | 0 | `b92d9aa056a97686a6ff3027bdbe09216d82edbc` |

64597 audits all **50 new theorems** and the reused retry/run definitions; 64598 audits the recovered sampler/consumer cohort. All reported axiom sets are subsets of `{propext, Classical.choice, Quot.sound}`. 64599 is the **one final diagnostic job manifest replay**, not a privacy-release replay; the import-only manifest adds no theorem. `final-post.json` verifies **1,001 current objects**, their source/direct/transitive dependencies and sidecars with **zero mismatches**. Native10 separately checks 16,314 external sidecar records and 16,329 prior pinned-sidecar records (overlap allowed), zero mismatches.

Every admitted scope uses MemoryHigh6G,MemoryMax8G,MemorySwapMax0,TasksMax64; Lean -M7000, one scope at a time. The 64536 reservation refusal was a vanished unrelated cgroup; no compiler/scope started. Its JSON/log were preserved, then the same ID was retried only after the full 180-second cooldown and a fresh admission. 64521 initially failed wrapper dependency lookup **before** a scope (an overbroad rebuild plan included a consumer outside the validated closure); the plan was restricted, the excluded consumers separately preflighted, and fresh admission used. No such prelaunch failure is counted as a Lean attempt or given credit.

Failed Lean 64500/64501 (recorded above),64532 (unqualified bind name),64541 (reserved continue identifier) remain reviewable and uncredited; changed replacements passed. Native03 used the wrong local libc-constant search path; native07 expected absent registry checksum metadata; both are uncredited and replaced with exact stdlib-lock/archive verification. Early baseline revision labels are qualified: source/dependency hashes and per-attempt snapshots pin the dirty inputs, not a claim those inputs existed at the baseline commit.

**Before/after:** no headline premise removed, added, weakened or reclassified as trust. V038,V178/V181,V347–V351 and all named native/composition/failure obligations remain P. T remains exactly entropy_law,entropy_kernel,observation; V370 is named and retained. The inherited restored V229,V230,V256,V257 credit is not withdrawn or re-adjudicated here. No crates/programs, existing proofs, simulator or observer were edited. The source-authority replay finding stops the full deployed endpoint step under h5′ and the no-edit rule; local independent source work has continued. The requested whole honest diagnostic law and full client-observer composition remain unfinished. Remaining compile allowance is not presented as exhaustion or used for unchanged regressions.


`cleanup.json` pins and removes only 42 private compiled artifact files, 856 private links and this job's control executable. Shared cache targets, source, receipts and all keys are retained. All evidence files are below20MB; no binary/olean/archive is committed. `COMMITS.txt` records the source-stage history; the final evidence/report commit is the branch tip. Nothing was pushed or merged.

Next concrete deliverable: obtain a corrected EJR-authoritative V2 source/cohort decision, re-elaborate its ten blocked consumers unchanged, and complete the emitting native leaves and original-L1 joint law before installing the complete RunJoin observer transport. This report does not claim the requested full composition or privacy target is achieved.
