# PV_DIAG5 — D452 resumed diagnostic work

Target not yet established. Branch `codex/pv-diag5-20261029`, base `b02602fa23`, exact sparse worktree `/Users/dominic/ZK/.worktrees/pv-diag`.

## Stage 1: h5 double-prime source correction

`statement-identity.json` mechanically checks both declarations (complete binders, types and statements) byte for byte. The complete source delta is exactly removal of one `rfl` after the closing `simp only`, inside the second proof. `V2-proof-only.diff` records it. The unchanged signatures are SHA256 `6af2396122c81e6597df5cbf8a0ca1e29a563f6d7d8cd9e2881250051ba4dd80` and `839cf3145d8de676e6e3abbfebaa3d0ebcc1d256e21f36ab19872f5853d73f00`. Commit `e030a78a739b65afe67a6e2641be1c8b3e25cb70` supplies the tracked-history explanation; its parent is the EJR variant. Research, candidate, worktree and the fixing commit have the identical tracked bytes.

The EJR entry is **stale**: source SHA256 `4321909f01b6f4d578b5e4c2198ba59406418ef8bd85f6e177f34ae107ddb694`, blob `431494fb8678733178af8c5c58cb18fbcb49f3b9`. Under h5 double-prime the tracked source SHA256 `0bb8dcc74e6d33492d386582c06836aca1ee35fc61ce898cc3afb8f6d1b20e16`, blob `d555952917bff6d87a4701569e1da29e9042c338`, is the authority. Neither source was edited.

**65000–65010 all pass**: fresh tracked V2, then all ten blocked consumers fresh and unedited in `cohort-plan.json` order, ending in `PrivacyR1HeadlineDeployedReal` and `PV_RunJoin_Deployed`. Raw receipts contain complete source snapshots, direct dependency/sidecar hashes, command, exit, wall, peak RSS, swaps, revision and printed axioms. All reported axioms are subsets of `{propext, Classical.choice, Quot.sound}`. `cohort-preflight.json` checks 986 reused dependency objects and their recorded fingerprints; all 5,673 external objects pass before compiling. ID preflight found no collisions. Private sources/objects only; no shared replacement.

Two setup attempts failed before admission/compiler launch because this job initially selected the narrower TrustItems cache and omitted special endpoint roots. The traversal was corrected to use the full recorded resume cohort plus the eleven explicit source pins. These own-input preparation errors consume no Lean/native attempts. The recovered sampler generation authority from diag4 remains in force; no source or extraction was changed.

The stale EJR obstruction is resolved. This replay discharges no native privacy premise by itself. Further diagnostic work follows below.

## Stage 2: capture, emitting operations and native bindings

`PV_DIAG5_Frame` proves that the normally completed callback sequence preserves the exact raw-frame order and that its first-match `actual_start` stays within the captured vector. `actual_display_slice_valid` excludes the short-format slice panic for those constructed states. Full format keeps all frames; short format keeps the actual suffix, including an empty suffix when the first match is the last frame. No lemma makes the actual raw PCs public.

`PV_DIAG5_Callback` follows clone → push → ORIGINAL-frame symbol_address → first-match test → post-push length → true. Every abnormal callee prefix is retained, with no later call fabricated. These are source control/ownership laws parameterized by complete callee executions; clone, allocation, push ownership cleanup, unwinding and foreign callbacks are not declared silent.

`PV_DIAG5_Emit` follows the fallible per-frame/per-symbol printing loops and proves leaf-coupled iteration. Errors stop the suffix. Panic, abort and divergence retain their prior operation traces. `PV_DIAG5_Display` binds the disabled/unsupported literal arms and the enabled/forced capture control; captured formatting forces resolution, selects full/short frames and executes current_dir. Invalid abstract short slices still panic. `PV_DIAG5_Cleanup` keeps CWD Result destruction after normal returns INCLUDING formatter errors; panic unwinds; abort and divergence do not run cleanup. The concrete allocator, formatter, resolver, locks/TLS, errno/I/O and destructor operations remain P.

`source-bindings.json` pins six COMPLETE deployed rust-src 1.94.1 regions, their file hash and statement mapping. These are **own-1 structural source associations with named callee obligations**, not complete reached-cone proofs. In particular the mutable writes in lazy_resolve are explicitly retained and no extracted iterator-restoration credit is asserted. V370 / pending D381/D386 is named and retained.

`native-controls.json` is **finite native validation**, not singleton-domain evidence or an honest proving-run distribution. The optimized rustc1.94.1 std-only harness checks 1,533 reference first-match sequences and actual std disabled/forced capture formatting, including early formatter error. Its exact source, binary hash, toolchain/profile and output are recorded. Application feature/profile inventory and shipped artifact `fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348` are inherited; this harness does not rebuild that application or establish shipped codegen equality. No crates/programs file changed.

## Named client outputs and composition boundary

`ClientOutput.execution`, `clientEvents`, `clientTerminal`, `clientFrames`, `clientDelivered`, `clientRequested` and `clientPieces` retain the native events and terminal alongside the existing public attempt count. They use PV_DIAG3 types directly. `decoder-handoff.json` identifies `PV_RJ4IDB.diagTrace`, `diag_events` and `diag_prefix` as the existing consumer; no decoder is copied or implemented here. At base b02602fa23 the PV_RJ4IDB files are not in the candidate tree. Their branch was read with git show only and pinned for handoff; no object or source from that branch is imported.

`honest_client_pieces` states the original-L1 joint interface and explicitly RETAINS nativeDiagnosticLaw and nativeTerminalLaw. It does not discharge them, add coins, alter an experiment or add an epsilon term. `joint_frame_emission` composes concrete per-frame operation couplings conditionally; the native print/resolver occurrence and coupling instance remains open. Existing D163 count laws and V394 disclosure are reused as inputs, not re-proved.

`deployed_result_collision_requires_prefix` freshly checks the exact actual `PV_RunJoin_Deployed.execute` boundary: a decoder of its Result alone can represent two prefixes only if those prefixes agree whenever Results collide. The further existing disclosed/oracle pair and decision equalities are audited separately. These are interface necessities, not native counterexamples or completed V038 refinement. Returned Result equality cannot erase prior bytes, frames, allocation requests, crashes or emitting divergent prefixes.

**The requested whole honest native diagnostic distribution and full client-observer composition remain unfinished.** The endpoint still needs source-faithful operations for the full reached cone, honest occurrence/terminal/frame/failure coupling on the original L1 coins, concrete disclosed/observerOracle prefix recovery, V036–V038 marginals/refinement and option-B witness-independent failure V336–V339. V347–V351 still own entered/rejected prefixes and ActivePole witness-trace coupling. No headline premise is removed, added, weakened or moved into T. T remains exactly entropy_law, entropy_kernel, observation.

## Per-sink disposition

All inherited scoped proofs retain their original assumptions. No conservative sink inventory is promoted to a complete linked/foreign/crash-effect enumeration.

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


New refinements: the Backtrace::Display short-slice panic is **NOT REACHED (proved)** for finite normally completed capture-callback states, with the native constructor/resolve length association retained. Disabled/unsupported display has **public-only selected literal (proved at source control level)**; full delivered-content/occurrence is UNRESOLVED. Captured full/short formatting and CWD cleanup remain **UNRESOLVED** for native honest joint privacy; their conditional complete-exit control laws are proved. All other dispositions above are unchanged.

No checked same-public honest-witness native diagnostic leak was found. The stale-EJR finding was resolved by h5 double-prime, not concealed or converted into a native leak finding.
