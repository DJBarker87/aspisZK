# Stream B deployed-body audit — LOG D375

**Target not yet established. 25 STANDS; 41 SUSPENDED across 66 scoped entries.** These are configuration/body-transfer dispositions, not new privacy closures.

Source `f849aef83e48e50062dbd83bb25497691c51e229`; branch `codex/pv-fscan-20261028`; worktree retained exactly as assigned. No crates/ or programs/ edit. No push.

## Suspensions first

**Measured normalized/concrete MIR differences:** V164, V169, V170, V178, V181, V182, V183, V184, V186, V187, V195, V198, V201, V216, V219, V220, V221, V222, V229, V230, V231, V233, V236, V238, V239, V240, V242, V247, V256, V257, V258, V259, V260, V265.

**Unresolved correspondence (no deployed credit; not a counterexample):** V197, V212, V213, V217, V218, V237, V246.

Each suspended row needs its original native link rebuilt/rechecked under the exact deployed configuration or a completed identity proof. No such Kani re-verification ran here. Existing Lean/model/source laws are not refuted or deleted.

The feature-only control found **no changed bodies in the resolved credited row envelopes** when toggling optimized-terminal while holding compiler and dependencies fixed. Global CT, prover/verifier and optimization body differences remain in the function matrices. Most matched extraction manifests already selected CT arithmetic and release/unchecked arithmetic. Do not describe all Stream B evidence as default-feature builds.

The stricter historical/deployed comparison also covers Rust 1.98 extraction/native fixtures versus Rust 1.94.1 deployment, std/alloc bodies, and actual dependency resolution. For example, `Public::transition` changes a `no_retag copy` instruction; `context_eq` changes StorageLive/StorageDead placement. These are body-identity failures, **not demonstrated value or privacy failures**. Symbol-only changes and unresolved edges are separately retained.

## Exact deployed configurations

| Artifact | Root / explicit selection | Effective project features / profile |
|---|---|---|
| devnet_spend | tools/r1-cost-probe; r1p-check,aspis-r1-cost-probe/ct-host-prover; --bin devnet_spend | core: ct-host-prover,r0; prover: ct-host-prover,insecure-spend-fixture,prover,r0; probe: ct-host-prover,default,private-leaf-salts,prover,r1p-check; statement: pool-v1-kernel,r0; release opt3, assertions/overflow off; rustc1.94.1 |
| default and devnet verifier | programs/r1-cost-probe; pool-adapter,private-leaf-salts | probe: default,optimized-terminal,private-leaf-salts,program-build; core:r0; statement:r0,pool-v1-kernel plus twelve optimized features; SBF release, toolchain1.89.0-sbpf-solana-v1.52 |
| Pool | programs/aspis-pool; r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit | default, pair-forest-account-evidence,pair-forest-verifier-lane-invariant-audit plus explicit features; core:[]; statement:pool-v1-kernel; same SBF release policy |

Every crate/version/feature list and effective profile is retained in `artifacts/units-{client-bin,default,devnet,pool}/features.json`; metadata JSON is compressed beside it. Workspace-wide metadata over-unifies unrelated members (including spend-dynamic-rate512) and is **not** the authority for package selection. Package-specific unit graphs correct it. The first client graph included all binaries; client-bin is the exact final entrypoint capture.

**Dependency drift matters:** the standalone client resolves zeroize **1.9.0**, while historical wrappers commonly pin **1.8.1**; GenericArray0.14.7 enables more_lengths/zeroize in the client. `libraries-client194-exact` records rustc artifact filenames, package IDs and exact features, avoiding selection by an old cache filename. Earlier `libraries-deployed`, `libraries-dev` and `libraries-default` are 1.8.1 controls, not the final deployed-dependency capture.

Default/devnet program feature sets agree; their deployment IDs differ as recorded in NCR and the retained release receipts. Historical ELF pins are unchanged; no ELF rebuilt by this audit. No host MIR result attests SBF lowering, syscalls, allocator or ABI.

## Inventory and comparison method

`native-evidence-index.json` indexes 3049 native command records across 18 closure-owning lanes, with receipt paths/SHA256, commands, explicit features, profile evidence and historical manifest associations. This deliberately includes duplicate wrappers, failures and supporting checks. It is not a count of credited passes. `configuration-source-facts.json` retains wrapper/profile definitions; 34 locked retained manifest graphs resolved, with three explicit online recoveries after offline cache misses.

MIR was emitted on the host with rustc1.94.1 under release and controlled historical feature/profile variants, plus the pinned nightly extraction cohort and reconstructed standard libraries. Per-function pairs include hashes; full text dumps are compressed with SHA256/size in dump-manifest.json. Ordinary operations, assertions, unwind edges, storage statements and `no_retag` are not erased. Impl source locations map to exact impl headers; per-body allocation labels are alpha-renamed. Zeroize version-path labels are normalized; its added ?Sized allowance is compared only on the original retained Sized/byte-array domain.

Reached lists are conservative static MIR envelopes. Ambiguous printed symbols and indirect callbacks are explicit, not silently resolved as favourable bodies. Exact changed matches and unmatched identities are separate in scan.json; all candidate alternatives and unresolved calls remain in reached-audit.json.xz. A suspended disposition is sufficient to withhold transfer, but this is not an exhaustive dynamic-body certificate for unresolved cones. Explicit parametric callbacks preserve the original theorem boundary and are not native callback implementations.

The non-generic statement equality wrapper is byte-identical across compiler cohorts, but still calls LiveSnapshot/VerifiedAfterstate PartialEq out of line. It does not clear V246. Matching parse/inverse wrappers likewise do not clear their callees. The context-equality probe differs in storage-lifetime placement. See concrete-results.json and both concrete scope receipts.

NCR and the subsequently available NCS method/handoff were read via git show; revisions and hashes are in reference-audits.json. NCS establishes selected-source cfg hashes and retains external/compiler boundaries. This audit additionally retains MIR/profile and dependency/cohort differences rather than calling them behavioural counterexamples.

## Per-row dispositions

| Row | Disposition / basis | First exact changed function or unresolved call |
|---|---|---|
| V164 | SUSPENDED — DIFFERENT NORMALIZED MIR | `core::non_null::<library/core/src/ptr/non_null.rs::impl<T: PointeeSized> NonNull<T>>::cast(_1: NonNull<T>) -> NonNull<U>` |
| V169 | SUSPENDED — DIFFERENT NORMALIZED MIR | `core::mem::replace(_1: &mut T, _2: T) -> T` |
| V170 | SUSPENDED — DIFFERENT NORMALIZED MIR | `alloc::raw_vec::<library/alloc/src/raw_vec/mod.rs::impl<A: Allocator> RawVecInner<A>>::non_null(_1: &RawVecInner<A>) -> NonNull<T>` |
| V177 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V178 | SUSPENDED — DIFFERENT NORMALIZED MIR | `alloc::layout_array(_1: usize, _2: core::alloc::Layout) -> Result<core::alloc::Layout, TryReserveError>` |
| V179 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V180 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V181 | SUSPENDED — DIFFERENT NORMALIZED MIR | `alloc::layout_array(_1: usize, _2: core::alloc::Layout) -> Result<core::alloc::Layout, TryReserveError>` |
| V182 | SUSPENDED — DIFFERENT NORMALIZED MIR | `core::non_null::<library/core/src/ptr/non_null.rs::impl<T: PointeeSized> NonNull<T>>::cast(_1: NonNull<T>) -> NonNull<U>` |
| V183 | SUSPENDED — DIFFERENT NORMALIZED MIR | `alloc::layout_array(_1: usize, _2: core::alloc::Layout) -> Result<core::alloc::Layout, TryReserveError>` |
| V184 | SUSPENDED — DIFFERENT NORMALIZED MIR | `alloc::raw_vec::<library/alloc/src/raw_vec/mod.rs::impl<A: Allocator> RawVecInner<A>>::capacity(_1: &RawVecInner<A>, _2: usize) -> usize` |
| V185 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V186 | SUSPENDED — DIFFERENT NORMALIZED MIR | `alloc::raw_vec::<library/alloc/src/raw_vec/mod.rs::impl<T, A: Allocator> RawVec<T, A>>::new_in(_1: A) -> RawVec<T, A>` |
| V187 | SUSPENDED — DIFFERENT NORMALIZED MIR | `alloc::raw_vec::<library/alloc/src/raw_vec/mod.rs::impl<A: Allocator> RawVecInner<A>>::capacity(_1: &RawVecInner<A>, _2: usize) -> usize` |
| V195 | SUSPENDED — DIFFERENT NORMALIZED MIR | `core::len_mismatch_fail::do_panic::runtime(_1: usize, _2: usize) -> !` |
| V197 | SUSPENDED — UNDETERMINED CORRESPONDENCE: unresolved symbol, declaration identity or call target; no deployed credit | `see unmatched identities / unresolved edges` |
| V198 | SUSPENDED — DIFFERENT NORMALIZED MIR | `core::len_mismatch_fail::do_panic::runtime(_1: usize, _2: usize) -> !` |
| V199 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V201 | SUSPENDED — DIFFERENT NORMALIZED MIR | `core::raw::from_raw_parts(_1: *const T, _2: usize) -> &[T]` |
| V202 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V204 | STANDS — NO NATIVE CLAIM | `identical within retained source-law boundary` |
| V205 | STANDS — NO NATIVE CLAIM | `identical within retained source-law boundary` |
| V206 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V208 | STANDS — NO NATIVE CLAIM | `identical within retained source-law boundary` |
| V209 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V210 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V211 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V212 | SUSPENDED — UNDETERMINED CORRESPONDENCE: unresolved symbol, declaration identity or call target; no deployed credit | `see unmatched identities / unresolved edges` |
| V213 | SUSPENDED — UNDETERMINED CORRESPONDENCE: unresolved symbol, declaration identity or call target; no deployed credit | `see unmatched identities / unresolved edges` |
| V214 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V215 | STANDS — NO NATIVE CLAIM | `identical within retained source-law boundary` |
| V216 | SUSPENDED — DIFFERENT CONCRETE MIR: context_eq storage lifetime placement differs between compiler cohorts | `see concrete-results.json` |
| V217 | SUSPENDED — UNDETERMINED CORRESPONDENCE: unresolved symbol, declaration identity or call target; no deployed credit | `see unmatched identities / unresolved edges` |
| V218 | SUSPENDED — UNDETERMINED CORRESPONDENCE: unresolved symbol, declaration identity or call target; no deployed credit | `see unmatched identities / unresolved edges` |
| V219 | SUSPENDED — DIFFERENT NORMALIZED MIR | `core::non_null::<library/core/src/ptr/non_null.rs::impl<T: PointeeSized> NonNull<T>>::cast(_1: NonNull<T>) -> NonNull<U>` |
| V220 | SUSPENDED — DIFFERENT NORMALIZED MIR | `aspis_core::evaluate_state_only_polynomial::{closure#0}(_1: &{closure@crates/aspis-core/src/state_only_sumcheck.rs:169:23: 169:37}, _2: usize) -> QM31` |
| V221 | SUSPENDED — DIFFERENT NORMALIZED MIR | `core::non_null::<library/core/src/ptr/non_null.rs::impl<T: PointeeSized> NonNull<T>>::cast(_1: NonNull<T>) -> NonNull<U>` |
| V222 | SUSPENDED — DIFFERENT NORMALIZED MIR | `zeroize::<registry/zeroize/src/lib.rs::impl<Z> Zeroize for Z where     Z: DefaultIsZeroes,>::zeroize(_1: &mut Z) -> ()` |
| V223 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V224 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V226 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V227 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V229 | SUSPENDED — DIFFERENT NORMALIZED MIR | `alloc::layout_array(_1: usize, _2: core::alloc::Layout) -> Result<core::alloc::Layout, TryReserveError>` |
| V230 | SUSPENDED — DIFFERENT NORMALIZED MIR | `alloc::layout_array(_1: usize, _2: core::alloc::Layout) -> Result<core::alloc::Layout, TryReserveError>` |
| V231 | SUSPENDED — DIFFERENT NORMALIZED MIR | `core::_mm_blend_epi16(_1: core_arch::x86::__m128i, _2: core_arch::x86::__m128i) -> core_arch::x86::__m128i` |
| V233 | SUSPENDED — DIFFERENT NORMALIZED MIR | `block_buffer::sealed::<registry/block-buffer-0.10.4/src/sealed.rs::impl Sealed for super::Eager>::split_blocks(_1: &[u8]) -> (&[GenericArray<u8, N>], &[u8])` |
| V234 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V235 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V236 | SUSPENDED — DIFFERENT NORMALIZED MIR | `digest::wrapper::<registry/digest-0.10.7/src/core_api/wrapper.rs::impl<T> Update for CoreWrapper<T> where     T: BufferKindUser + UpdateCore,     T::BlockSize: IsLess<U256>,     Le` |
| V237 | SUSPENDED — UNDETERMINED CORRESPONDENCE: unresolved symbol, declaration identity or call target; no deployed credit | `see unmatched identities / unresolved edges` |
| V238 | SUSPENDED — DIFFERENT NORMALIZED MIR | `core::len_mismatch_fail::do_panic::runtime(_1: usize, _2: usize) -> !` |
| V239 | SUSPENDED — DIFFERENT NORMALIZED MIR | `alloc::layout_array(_1: usize, _2: core::alloc::Layout) -> Result<core::alloc::Layout, TryReserveError>` |
| V240 | SUSPENDED — DIFFERENT NORMALIZED MIR | `core::non_null::<library/core/src/ptr/non_null.rs::impl<T: PointeeSized> NonNull<T>>::cast(_1: NonNull<T>) -> NonNull<U>` |
| V242 | SUSPENDED — DIFFERENT NORMALIZED MIR | `aspis_statement::pair_forest_semantic_terminal::r0::<crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs::impl<'a> Public<'a>>::transition(_1: pair_forest_semantic_` |
| V246 | SUSPENDED — UNDETERMINED CORRESPONDENCE: unresolved symbol, declaration identity or call target; no deployed credit | `see concrete-results.json` |
| V247 | SUSPENDED — DIFFERENT NORMALIZED MIR | `aspis_statement::state_only_copy_helper_sum::{closure#0}(_1: {closure@crates/aspis-statement/src/state_only_semantic.rs:584:35: 584:37}) -> aspis_core::field::QM31` |
| V254 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V256 | SUSPENDED — DIFFERENT NORMALIZED MIR | `aspis_r1_cost_probe::sampler::low_base_p_digits::{closure#0}(_1: &mut {closure@crates/aspis-r1-cost-probe/src/sampler.rs:58:30: 58:33}, _2: usize) -> u32` |
| V257 | SUSPENDED — DIFFERENT NORMALIZED MIR | `aspis_r1_cost_probe::sampler::low_base_p_digits::{closure#0}(_1: &mut {closure@crates/aspis-r1-cost-probe/src/sampler.rs:58:30: 58:33}, _2: usize) -> u32` |
| V258 | SUSPENDED — DIFFERENT NORMALIZED MIR | `alloc::raw_vec::<library/alloc/src/raw_vec/mod.rs::impl<A: Allocator> RawVecInner<A>>::non_null(_1: &RawVecInner<A>) -> NonNull<T>` |
| V259 | SUSPENDED — DIFFERENT NORMALIZED MIR | `alloc::alloc::<library/alloc/src/alloc.rs::impl Global>::alloc_impl_runtime(_1: core::alloc::Layout, _2: bool) -> Result<NonNull<[u8]>, core::alloc::AllocError>` |
| V260 | SUSPENDED — DIFFERENT NORMALIZED MIR | `aspis_r1_cost_probe::weights::<crates/aspis-r1-cost-probe/src/weights.rs::impl Weights>::raw::{closure#0}(_1: &mut {closure@crates/aspis-r1-cost-probe/src/weights.rs:229:37: 229:42` |
| V261 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V264 | STANDS — SAME RESOLVED BODIES at the existing source-law boundary; explicit parametric callbacks remain parametric | `identical within retained source-law boundary` |
| V265 | SUSPENDED — DIFFERENT NORMALIZED MIR | `aspis_r1_cost_probe::sampler::circle_sample::{closure#0}(_1: {closure@crates/aspis-r1-cost-probe/src/sampler.rs:122:79: 122:82}, _2: CirclePointError) -> SecureCirclePoint` |
| V270 | STANDS — NO NATIVE CLAIM | `identical within retained source-law boundary` |

The complete exact matched-function lists, selectors, original/deployed hashes, source scopes and next actions are in scan.json. Full bodies are in changed-bodies.json.xz / changed-library-bodies.json.xz and the raw MIR blobs. Neither unchanged source laws nor narrowed native domains are promoted to whole deployed execution.

## KMX re-verification items

| Row | Historical outcome | Deployed transfer under (x) |
|---|---|---|
| V178 | unconfirmed (timeouts) | UNDETERMINED; not newly credited under (x) |
| V179 | confirmed stubbed PASS with matched failing controls | UNDETERMINED; not newly credited under (x) |
| V182 | whole row unconfirmed; partial windows passed | UNDETERMINED; not newly credited under (x) |
| V195 | confirmed stubbed PASS with matched failing controls | UNDETERMINED; not newly credited under (x) |
| V233 | confirmed split windows with matched failing controls | UNDETERMINED; not newly credited under (x) |

The exact KMX patch remains bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; matched failing controls and original outcomes are retained by their original receipts. No K-1/K-2 qualification is lifted. A standing independent structural/source link does not automatically re-credit its separate historical Kani build. The concrete serializer feature/profile control has identical optimized MIR; that does not certify the complete instrumented Kani sysroot/harness graph.

## Receipts, limitations and next action

Native capped scopes recorded: 67/150. Kani verification: 0/0. Lean: 0/10; no env-J ID consumed. Every native launch records its exact target, exit, wall, RSS, swap and source revision, with axioms N/A, under 6G high/8G max/swap0/Tasks64 and successful pre-admission plus barrier. scopes.json is the compact receipt index; raw receipts remain beside each run.

Failed diagnostic inputs and superseded parser outputs are retained. The non-CT r1p-check control is not buildable at this candidate (host CT-dependent code); the deployed CT build succeeded. A mistaken transitive feature spelling and a private-path serializer import were corrected in distinct runs. Intermediate function-key collisions, missing row root and receiver/root selection errors were corrected before the final report. Source-only uploads did not each have fresh pretransfer admission snapshots; all compiler launches did. No cap increase, unchanged failed build replay, proof replay or source implementation repair occurred.

Before/after endpoint premises: removed0, added0, changed0. Retained: deployed source/executable association, E1/E2, real RunJoin, the client route, L1/L2/L3, and exactly entropy_law/entropy_kernel/observation in T. No simulator or observer weakened. No wallet/account key created or cleaned.

Next concrete deliverable: rebuild the suspended native links with the exact client feature/dependency graph, rustc1.94.1 and release profile, preserving each original domain, resource/world model and substitutions. For unresolved cones recover/resolve the exact missing symbols and historical source/harness associations first; do not infer mismatch or proof from a missing file. Any future Kani replay needs a new authorized verification budget and the existing copy/negative-control and function-pointer restrictions. Target remains not yet established.

Final integrity validation: [validation.json](validation.json) PASS. All 517 mirrored runtime source files match the candidate; cleanup.json records exact tool versions, no live own compiler and deletion only of owned rebuildable targets. The repository Cargo config contains only an xtask alias, with no build/profile overrides. No additional replay is pending in this job.
