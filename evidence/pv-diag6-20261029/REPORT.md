# PV_DIAG6 — D454 diagnostic continuation

Target not yet established. Exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-diag`, branch `codex/pv-diag6-20261029`, base `19b2164e3d`. V2 is done and is not replayed.

## Native joint-event and terminal control

`PV_DIAG6_Native` supplies named joint laws for unwind, lexical scope, write-all step and arbitrary finite write prefixes, dynamic/static formatting, adapter error storage, stderr capture dispatch, ignored write Results and owned Termination reporting. The relational contracts retain ordered events, final state and terminal together. All primitive native callee coupling laws remain explicit hypotheses. In particular these are **control composition laws, not concrete native privacy instances**.

The abnormal leaf, Interrupted guard and Interrupted-error destruction laws retain precisely the already-emitted prefix on panic, abort or divergence. The adapter retains error-slot replacement effects; formatting and capture failures do not fabricate later calls. Existing source regions are rechecked in `source-bindings.json` against deployed rust-src1.94.1/dependency file hashes, retaining allocator, syscall/errno, vtable/drop, formatter/lock/TLS and memory-validity obligations. V370 / pending D381/D386 remains P. The inherited feature inventory is recorded; no shipped code or feature selection changed.

65200–65207 freshly rebuild the eight smallest inherited model modules. 65208 failed because the unwind proof had not unfolded the model; corrected65209 passes. 65211 failed on a reduced Nat match before the conditional split; corrected65212 passes. No failed object is consumed. 65210 and65213–65242 pass, adding one control/terminal law per incremental source change. native01 rechecks ten complete source regions; it is a source-association check, not runtime or singleton-domain evidence.

Further stages and final audit follow below.

## Failure and divergence prefix recovery

`PV_DIAG6_Prefix` defines a proof relation for ordered list prefixes and a coherent family of finite execution observations. It proves lossless recovery for each family member, permanence and order of all prior emissions, cleanup panic/abort/divergence, partial writes and Interrupted-error destruction. The model result `no_finite_summary_for_unbounded_emissions` forbids replacing an unbounded emitting history with one fixed finite prefix. It is not a native counterexample.

`recover` is a parameter for the existing decoder's errorsStderr3 projection, whose universal equation is `PV_RJ4IDB.diag_events`. No decoder is duplicated. The candidate tree at19b2164e3d still lacks all actual PV_RJ4IDB modules; the inherited read-only branch snapshots identify the consumer. Integration and concrete runtime.disclosed/observerOracle recovery remain P, rather than being inferred from these parameterized laws. 65243,65245–65268 pass;65244 failed on the orientation of list append associativity and was corrected before use.

A first stage commit was delayed by an own-input sparse path omission; `git sparse-checkout add evidence/pv-diag6-20261029` resolved it. No full checkout or compiler launch was involved.

## Whole-law transport through the existing L1 operators

`PV_DIAG6_Distribution.honest_joint_native` retains the existing D163 L1 count equation plus **nativeDiagnosticLaw** and **nativeTerminalLaw**, at precisely the same public-data/coin coordinates. The latter two hypotheses are NOT discharged. `whole_diagnostic_law` and `whole_prefix_family_law` transport the full count/events/terminal output and the entire prefix function using the existing R0Z finite-law operator. Every test and rational expectation follows from that joint equation, rather than from marginal count equality. These are symbolic finite-carrier theorems; no large tape enumeration is performed.

The existing R0Z law/mass/expectation closure is reused read-only after a29-object h6 preflight, including all three project-source pins and dependency hashes (`law-preflight.json`). It is the same finite operator used by D163. Neither D163's retry/count laws nor its still-open native L1 instance is re-proved. V394's public count disclosure is reused; it is not a finding. Source65279 failed on a malformed projection in the prefix-family binder; corrected65280 passes.65269–65278 and65280–65296 pass.

`decoder-handoff.json` names each new export and the exact existing PV_RJ4IDB consumer instantiation. There is no decoder implementation here. The decoder/decision laws cover diagnostic pieces only; whole client cross-channel assembly and actual disclosed/oracle recovery are still required. Native03 is an optimized rustc1.94.1 std-only harness: four finite controls preserve actual delivered prefixes through partial writes, Interrupted retry, writer panic and dynamic formatting failure. It is finite validation, with source/binary/toolchain hashes, not a universal law or shipped application codegen identity.

**The whole honest native diagnostic distribution remains unproved.** The honest native event/terminal instances, complete native prefix-family association and actual observer recovery cannot be inferred from control composition or finite controls.

## Per-sink disposition

All inherited assumptions and source-association boundaries remain. The following complete inherited inventory is retained; new joint-control/prefix transport does not establish the missing native honest instances.

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

Capture short-slice panic remains NOT REACHED under the inherited finite normal callback/constructor association. Disabled/unsupported display remains public-only selected literal at source-control level, with occurrence and delivery UNRESOLVED. Formatting CWD, resolved frame and destructor effects remain UNRESOLVED for native honest joint privacy. No checked same-public honest-witness leak was found. No Kani was run; no quarantined Kani result is claimed.

## Endpoint premises and remaining work

Before/after: no premise of `PrivacyR1HeadlineDeployedReal.privacy_headline_deployed` or its native deployment refinement is removed, added, weakened or reclassified as trust. T remains exactly entropy_law, entropy_kernel, observation. The new propositions organize conditional proof obligations and are not endpoint discharge. V038,V178/V181,V336–V339,V347–V351,V370 remain named. Existing V229,V230,V256,V257 credit is untouched.

Next concrete deliverable: instantiate the complete primitive native couplings, including allocations/cleanup, locks/TLS/errno, raw unwinder/resolver/formatter and foreign/crash effects, then prove the native event/terminal and every-prefix laws on the original L1 coupling. Integrate the existing PV_RJ4IDB adapter and recover runtime.disclosed/observerOracle with V036–V038. The pending option-B failure event must itself be witness-independent.

Final verification and source identities follow below.
