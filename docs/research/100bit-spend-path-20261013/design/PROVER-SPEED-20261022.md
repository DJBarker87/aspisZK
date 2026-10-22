# Prover speed investigation — 2026-10-22

## Scope and stages

Measurement and analysis only. No shipped source changes, no Lean, no implementation or protocol adoption. Target: strictly under 15 seconds per proof, alongside the existing security contract.

Stage 1: pin research `7f13d411b8f6af7dbd17d23e79fd24bf9998e913` and v2 `2b7a80b65a` (resolved full revision in receipts), prepare scratch instrumentation and capped host runner. Stage 2: optimized repeated measurements, at least five transfer and five withdrawal proofs per variant, phase and retry accounting. Stage 3: rank proposals and assess proof bytes, source bindings, trust and L1/L2/L3 effects; stop.

Host: `dombarker@100.108.41.90`, dedicated job directory `/home/dombarker/project-offloads/codex-cx-prover-speed-20261022`. Every build/run is admitted within MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Cargo uses release and -j4. Expected heavy work: proof generation, including encoding and named P_R1 certificate generation/elimination, following a separate compilation stage. No dependency rebuild for Lean and no wallet key cleanup.

Measurements will use `prove_masked_retrying_with` and `generate_for_mask_nonce` with fresh public nonce identifiers and fresh OS private seeds. Fixture preparation and verification are outside the proof timer. These identifiers exercise the proof-account nonce interface but do not create, fund or publish Solana accounts; account provisioning and network publication are outside this measurement.

Evidence: `../evidence/prover-speed-20261022/`. Instrumentation is applied only to host scratch copies of pinned sources. Timings are measurements, not formal bounds or security evidence. Estimated savings will be explicitly labelled projections, not measured optimized results.

## Results (measurement)

**The under-15-second target is not met.** Twenty primary proofs completed: five transfer and five withdrawal proofs on each pinned variant, all with one attempt, 57,607 bytes and passing strict tx1/tx2 plus dense verification. These fresh-randomness fixture measurements do not bound retry tails or arbitrary witnesses.

| Variant | Fixture | n | Median s | Min–max s | Sample SD s | Attempts |
|---|---|---:|---:|---:|---:|---|
| research | transfer | 5 | 37.249790 | 37.161810–37.824086 | 0.272126 | [1, 1, 1, 1, 1] |
| research | withdrawal | 5 | 37.236374 | 37.099096–37.562710 | 0.178893 | [1, 1, 1, 1, 1] |
| v2 | transfer | 5 | 37.578734 | 37.276936–38.570364 | 0.533952 | [1, 1, 1, 1, 1] |
| v2 | withdrawal | 5 | 37.435241 | 37.345688–37.728689 | 0.150566 | [1, 1, 1, 1, 1] |

The samples ran research first, then v2, each as five alternating transfer/withdrawal pairs. They were not randomized between variants, cold-cache trials, CPU-pinned trials or a statistical equivalence study. The early warmup/drift and shared-host scheduling remain part of the spread. No v2 sample crossed the D168 +10% gate relative to its fixture’s research median.

### Phase medians (seconds; measurement)

Columns are research transfer / research withdrawal / v2 transfer / v2 withdrawal. Hierarchical rows marked “child” are included in their parent and must not be added again. Very small values retain six decimals so “zero” is not confused with unmeasured.

| Phase | Research T | Research W | V2 T | V2 W |
|---|---:|---:|---:|---:|
| Entropy (callback; OS nonce + two private seeds) | 0.000002 | 0.000002 | 0.000002 | 0.000002 |
| Durable reservation (file + directory fsync) | 0.006547 | 0.007472 | 0.005663 | 0.007725 |
| SeedExpander mask material after reservation | 0.000413 | 0.000385 | 0.000398 | 0.000384 |
| Profile21 zero-factor D expansion | 0.000065 | 0.000065 | 0.000060 | 0.000060 |
| Mask apply/audit and residual cleanup | 0.001505 | 0.001493 | 0.001492 | 0.001467 |
| Private salt derivation, three full arrays | 0.258067 | 0.257904 | 0.257646 | 0.257586 |
| Encoding-domain construction | 0.034461 | 0.034533 | 0.035245 | 0.035102 |
| C1+C2 commitments (parent) | 1.229692 | 1.230209 | 1.344226 | 1.348169 |
| ↳ 29 lane encodings (child) | 0.966417 | 0.965965 | 1.003645 | 1.008383 |
| Semantic build excluding commitments/sumcheck/pole (exclusive) | 0.001410 | 0.001415 | 0.001479 | 0.001485 |
| Pole check | 0.000125 | 0.000100 | 0.000104 | 0.000120 |
| Semantic sumcheck (parent) | 2.462385 | 2.438083 | 2.531160 | 2.506019 |
| ↳ Point claims (child) | 2.081789 | 2.063008 | 2.136271 | 2.129070 |
| ↳ Terminal evaluations (child) | 0.351740 | 0.348777 | 0.359389 | 0.348543 |
| Opening rounds + folds | 0.000282 | 0.000286 | 0.000290 | 0.000288 |
| Opening weights + materialization | 0.000531 | 0.000526 | 0.000519 | 0.000522 |
| Folded-word encoding | 0.097937 | 0.098098 | 0.096329 | 0.096657 |
| C1+C2 leaf assembly/hash (commitment child) | 0.217215 | 0.216839 | 0.294587 | 0.293673 |
| Folded leaf assembly/hash | 0.041046 | 0.041083 | 0.041027 | 0.041161 |
| All three Merkle parent trees (C1+C2 are commitment children) | 0.068164 | 0.068161 | 0.067942 | 0.067997 |
| Opening transcript (exclusive; semantic transcript below) | 0.000010 | 0.000011 | 0.000008 | 0.000008 |
| P_R1 total (parent) | 33.078059 | 33.086726 | 33.332005 | 33.129206 |
| ↳ P_R1 public_data (child) | 0.194097 | 0.188895 | 0.186269 | 0.194927 |
| ↳ P_R1 emit (child) | 12.286372 | 12.291624 | 12.299315 | 12.308752 |
| ↳ P_R1 convert (lane preparation + conversion) (child) | 4.749646 | 4.737363 | 4.712550 | 4.682215 |
| ↳ P_R1 build (child) | 7.124224 | 7.108381 | 7.130140 | 7.136988 |
| ↳ P_R1 check (child) | 8.799480 | 8.782284 | 9.009215 | 8.708897 |
| Publication: compact bytes + openings/multiproofs | 0.000126 | 0.000127 | 0.000129 | 0.000127 |
| Opening arithmetic/serialization residual (exclusive) | 0.003945 | 0.003896 | 0.004060 | 0.004041 |

The semantic sumcheck made 28,645 terminal calls and 28,646 point-claim calls per proof. `convert` includes `Lanes::new` just before conversion, as in the existing combined builder timer. P_R1 total also includes cleanup/catch/TLS overhead, so its timed children do not sum exactly to the parent. Exclusive timer sums agree with each end-to-end proof time within 1 ms (`summarize.py` checks this). Instrumentation overhead was not separately subtracted; this is a measured scratch binary, not a formal cost model.

### Supplemental subphase pass (one sample per fixture, measurement)

These four additional proofs fill the semantic-transcript and emitter-subphase timing gaps. They are not mixed into the primary medians above. All used one attempt and passed strict/dense verification.

| Variant | Fixture | Wall s | Semantic transcript s | Opening transcript s | Emit lifts s | Emit QPrime s | Emit BCond s |
|---|---|---:|---:|---:|---:|---:|---:|
| research | transfer | 38.109624 | 0.000026 | 0.000012 | 0.108816 | 6.883412 | 5.224782 |
| research | withdrawal | 37.084255 | 0.000021 | 0.000011 | 0.110278 | 6.872600 | 5.228728 |
| v2 | transfer | 38.127333 | 0.000020 | 0.000008 | 0.114715 | 6.840379 | 5.212850 |
| v2 | withdrawal | 37.853249 | 0.000026 | 0.000009 | 0.109248 | 6.861139 | 5.213768 |

Semantic transcript timers include validation/challenge work in its entry points and are nested in semantic sumcheck/build; opening transcript uses exclusive time to avoid nested method double-counting. Emitter lift/QPrime/BCond timers are the existing producer timings; their subtotal excludes some setup, lane tables and cleanup. The measured dominant emitter regions are QPrime (~6.9 s) and BCond (~5.2 s), not lifts (~0.11 s). Their internal elimination dependencies still constrain parallelism; this pass establishes no scaling result. Primary/fine source manifests differ only in `r1_wire.rs` and `z4/z9e.rs`, the supplemental timer sites.

### Critical-path arithmetic (projection)

* research transfer: P_R1 33.078 s, remainder 4.172 s. Even making all non-P_R1 work free leaves 33.078 s. Holding the remainder fixed needs **>3.05×** P_R1 acceleration to get strictly below 15 s; 4× projects 12.441 s for one attempt.
* research withdrawal: P_R1 33.087 s, remainder 4.150 s. Even making all non-P_R1 work free leaves 33.087 s. Holding the remainder fixed needs **>3.05×** P_R1 acceleration to get strictly below 15 s; 4× projects 12.421 s for one attempt.
* v2 transfer: P_R1 33.332 s, remainder 4.354 s. Even making all non-P_R1 work free leaves 33.332 s. Holding the remainder fixed needs **>3.13×** P_R1 acceleration to get strictly below 15 s; 4× projects 12.687 s for one attempt.
* v2 withdrawal: P_R1 33.129 s, remainder 4.346 s. Even making all non-P_R1 work free leaves 33.129 s. Holding the remainder fixed needs **>3.11×** P_R1 acceleration to get strictly below 15 s; 4× projects 12.628 s for one attempt.

All observations used one attempt. For a k-attempt call, rejected work remains part of proof latency. These samples do not establish a rejection-rate distribution or worst-case under-15 bound; an eight-attempt cap is not itself such a bound. No acceptance check, fresh seed or ledger reservation was removed.

### Host and resource receipts (measurement)

Intel Core Ultra 7 155H, x86_64 Linux native, **16 physical cores / 22 logical CPUs** (hybrid topology). Rustc **1.94.1**, LLVM **21.1.8**. Release profile, `-j4`, locked dependency graph, `RUSTFLAGS=-C link-arg=-Wl,--threads=4`; research `optimized-terminal,r1p-check`, v2 `optimized-terminal,ct-host-prover`. Per-package checked overflow stays enabled for the extracted certificate crates. SHA-256 instruction excerpts and source/native binary hashes are retained; instruction presence is not proof of dispatch frequency or L3 constant-time behaviour.

| Primary process | Exit | Wall s incl. setup/verification | Peak RSS KiB | Cgroup peak bytes | Swap events | Observed thread counts |
|---|---:|---:|---:|---:|---:|---|
| research | 0 | 374.119 | 588732 | 611188736 | 0 | [1, 5, 11] |
| v2 | 0 | 377.145 | 570556 | 591761408 | 0 | [1, 5] |

Each build and run used MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. Build/run exits, GNU-time RSS, cgroup peaks and swap evidence are under `receipts/`. The initial finite-cap reservation including this job was 32.375 GiB against the 55 GiB limit; subsequent admissions are recorded. The whole route is not single-threaded: see the threading correction below. These are Rust measurements; `#print axioms` is N/A and no Lean job or formal release replay ran.


## Method and interpretation

The scratch timers nest: each entry records inclusive seconds, exclusive seconds and call count. Sum only exclusive entries; the retry-loop inclusive timer and end-to-end timer are separate cross-checks. Checker stderr records public-data, certificate emit, converter, extracted builders and checker timings. Subtraction from reservation-plus-mask-material gives mask-material work after the measured durable reservation. Semantic sumcheck includes separately timed claim evaluation and terminal evaluation. Publication means compact byte assembly and multiproof extraction, ending at return from the prover, not an RPC transaction.

Each variant runs in one fresh process containing five alternating transfer/withdrawal pairs. Thus process-local caches may warm across pairs; no CPU affinity or isolated-machine claim is made. The host has hybrid cores, background services and a scheduler, so ranges are descriptive. Randomized proof bytes differ naturally across attempts. Every returned proof is checked by strict tx1/tx2 and dense verification outside the proof timer. This is functional fixture measurement, not a proof of constant-time execution, an arbitrary-input bound, or byte-equivalence evidence for a future optimization.

## Source-based observations (analysis, not optimized measurements)

* `z4/z9e.rs::p_r1_check` serially calls `public_data`, `z9c::emit`, `z9d::convert`, `extracted_builders`, then `c3/check::check`. All of this lies inside each attempt. P_R1 failure, a pole or mask exhaustion retries with new secrets; the cap remains eight.
* `convert` materializes `own`, `round`, `tq`, `rel`, `gown`, `ground`, `gbat`, `lo`; `extracted_builders` then overwrites these fields with the extracted `fill_*` outputs. It also rebuilds family descriptors. There is repeated work, but conversion additionally produces/checks certificate shapes and intermediate values (`rho`, `E`, `beta`, `nm`), so deleting the converter is not an equivalent optimization.
* `c3/check::check` checks independent lift, QPrime and BCond components. `dot` and `kdot` are scalar M31 products; `prod_ok` supplies independent output-cell comparisons. These are plausible blocking/vectorization/parallelization targets. Checked overflow, canonicality, shape failures and panic-to-rejection semantics must survive.
* `z9c::emit` uses ordered, challenge-dependent elimination, pivot selection and early exits. Independent lift certificates can be distributed, but blindly parallelizing pivot updates does not establish an identical acceptance predicate or certificate. The existing public/private-coin simulatable-trace route from D166 still applies; padding these computations is not the selected strategy.
* Salt derivation calls `derive_pool_v1_leaf_salt` three times over 262,144 indices. Each call recomputes the same per-attempt binding hash before its unique salt hash. Hoisting the binding is a plausible subsecond saving; the ROM read history changes even if returned salt bytes match, and the adaptive-oracle refinement needs a transport argument.

## Proposal assessment framework

“Identical bytes” below means identical public statement, attempt seeds/nonces, challenge schedule, arithmetic and acceptance decisions produce identical serialized proof bytes. It is not a comparison between independently randomized proofs. A different internal host-only P_R1 certificate need not change proof bytes, but a different acceptance predicate can change which attempt is published. Do not infer protocol equivalence from fixture acceptance.

Preserving mathematical functions can retain their abstract Lean theorems. It does **not** retain the native source checksum or automatically bind the optimized implementation to those theorems. Relevant proof families are `R1Z/CertCheck{Dot,Mat,Ker,Top,Extracted}`, `CertBuild{Base,Tower,Fill,Extracted,Ident,Ident2,Chain}`, `CertCheckSound{Cols,Rel,Round,GBat,All}` and the `CertData`/`CertR1` joins. Changed native kernels require new Kani per-step/equivalence bindings to the owned/extracted reference (or extraction and proofs for new reference code), including checked arithmetic and every failure path. Unchanged CT field-kernel proofs may be reused only with their exact source/feature pins. Host changes require the existing verifier-ELF and deterministic proof/public-byte identity gates before adoption; this job runs no SBF or Lean release suite because it changes no shipped source.

For every byte-preserving proposal, retain L1 outcome/retry/error/reservation/publication laws and prove its L2 trace simulatable jointly with the FS transcript under D166. The secret-bearing field and pole arithmetic must remain CT. Re-pin compiler, flags, native binary and CPU, audit generated code and repeat appropriate L3 timing measurements after actual changes. These are future obligations, not results from this job.

Parallelism has an additional boundary: D133 and `PROVER-COMMIT23-20261021.md` assume a single live thread for TLS schedules. Keep the transcript, entropy/reservation, publication and any existing TLS keys on the invoking thread, and give workers explicitly owned immutable inputs and disjoint output buffers. This can limit the replacement to a worker-subsystem refinement, but cannot claim the current whole-invocation single-thread premise remains true. The checker also has a thread-local QUIET panic hook: workers must preserve suppressed panic details and deterministic fail-closed joining; parent TLS does not automatically configure child threads. Allocation, thread scheduling, joins, cancellation and logs become part of L1/L2 observations and the trusted std/runtime boundary. No such trust change is adopted here.

Changing the hash function, tree arity/leaf count, field, query count, sumcheck protocol, wire encoding, or weakening/removing P_R1 is outside byte-preserving host optimization. Flag for user approval: these change proof bytes and/or the accepted protocol and invalidate the corresponding verifier/soundness/privacy bounds and artifact pins. Dropping the checker is not an approved speedup.

## Merkle and salt operation counts (source analysis)

Each completed attempt constructs **three binary trees**, each with 262,144 leaves, 18 levels and 262,143 parent hashes. Total: 786,432 leaf hashes + 786,429 parent hashes = **1,572,861 tree hash calls**. With the exact current SHA-256 leaf widths (C1 480 value bytes, C2/folded 128), two-byte leaf domain and 32-byte salt, and 65-byte parent grammar, this is 5,505,018 SHA-256 compression blocks including padding. These are source-derived counts, not sampled performance counters or formal cost proofs.

Three complete salt arrays contain 786,432 salts. The current salt helper hashes both the attempt binding and unique salt each time: another **1,572,864 hash calls**, excluding mask seeds/expanders, transcript and challenge sampling. The padded folded domain still has 262,144 uniquely salted leaves; its 196,608 zero-valued leaves cannot reuse a common leaf hash. A change to 65,536 leaves would change roots, openings, proof bytes and the protocol. Detailed arithmetic is in `hash-counts.json`.

## Threading correction and trust scope

The whole route is **not single-threaded**. `z4/z9.rs::unit_functionals` uses four workers; `Lanes::new` spawns twelve lane workers and joins them in lane order, called inside emission and again before conversion. Thus source permits 13 live threads including the caller during lane-table construction. The research process sampled at one-second intervals recorded 1, 5 and 11 threads; this sampler can miss shorter peaks. The main semantic, encoding/Merkle, elimination, converter, extracted `fill_*` and certificate-checker loops remain serial except those existing helpers. A whole-run one-thread characterization would be false.

D133's single-thread TLS law therefore needs a boundary-specific interpretation for the existing P_R1 worker helpers already, not just proposed new parallelism. This report does not establish a leak or withdraw any theorem: the TLS theorem concerns one selected-thread schedule, while a complete native binding must show which callbacks touch that selected key. Reusing it for new workers requires explicit confinement or a concurrent refinement. The quiet-panic-hook worker issue is an existing scope question as well as a requirement for additional worker code.

## Ranked speedup candidates (projections; none implemented)

The following budgets use the repeated profile's approximately 33-second P_R1 and 4–5-second remainder. Multipliers are **hypothetical effective phase speedups**, not measured achievable hardware scaling. Ranges overlap and must not be added across rows. A fourfold improvement of P_R1 projects approximately 12–13 seconds end to end; a threefold improvement is around 15–16 seconds and does not reliably meet a strict under-15 requirement. No proposal is a performance guarantee, particularly on this hybrid CPU or with retries.

| Rank | Candidate and profile-based saving | Proof bytes / verifier / soundness | Existing bindings and trust | L1 / L2 / L3 consequences |
|---|---|---|---|---|
| 1 | **Parallelize the remaining P_R1 work**, targeting emission, conversion, extracted builders and independent checker rows/certificates. At 3–4× effective acceleration of ~33 s: **22–25 s saved**. Only the upper part of that range meets the target by itself; aim for P_R1 ≤10 s including overhead. Existing short parallel helpers do not imply these larger stages already scale. | Identical if ordered results, exact arithmetic, all shape checks, panic/rejection semantics and the acceptance predicate are preserved. Host certificates are not proof payloads. No verifier/protocol change under these conditions; otherwise flag approval. | Rebind worker schedules and native `CertBuild*`/`CertCheck*` callers, deterministic joining and error handling. Retain abstract algebra only after equivalence. Extend/confine the D133 TLS/std runtime boundary; worker QUIET must be explicit. | L1 preserve retries/errors/reservations and log suppression. L2 prove worker inputs/allocations/schedules simulatable jointly with challenges; no secret-bearing work moved to variable traces. L3 adds scheduler/runtime and multicore/cache behaviour; new binary/disassembly/timing evidence. |
| 2 | **Blocked or SIMD exact M31 matrix arithmetic** in extracted checker and builders, plus emitter row updates. The measured extracted checker+builders are ~16 s: a 2–4× improvement saves **8–12 s**; emitter acceleration can contribute separately from its ~12 s budget. This is a complement to row 1, not an additional disjoint 25 s. | Identical if each matrix entry and boolean/failure result is identical. Keep checked-overflow behaviour; delayed reduction must have proved accumulator bounds. Exact deterministic comparisons retained; no Freivalds/random checking. | New dot/kdot/reduction/vector lane Kani gates and Lean reference binding; re-pin `CertCheckDot/Mat/Ker`, `CertBuildBase/Tower/Fill` and dependent joins. A native fast implementation can bind to the existing owned reference rather than rewriting every abstract theorem. Single-thread SIMD does not add workers. | L1 same acceptance required. L2 public/challenge-driven traversal remains under D166, operand-secret kernels remain CT. L3 CPU instruction/dispatch and compiler CT trust changes; inspect vectors, reductions and variable-latency instructions. |
| 3 | **Remove duplicated source-column construction** between converter, emitter families and extracted builders, retaining certificate intermediates and checks. Converter budget ~4.7 s is an upper bound for its removal; **0–4.7 s saved**, with actual removable fraction unmeasured. Larger family reuse may overlap emission/building; do not claim it as extra measured saving. | Identical only if resulting `pb`, `cc`, failure semantics and acceptance match. The converter's `rho/E/beta/nm` and shape checks cannot be skipped. No on-chain change if equivalent. | Rebind `z9d::convert`/`z9e::extracted_builders` assembly, descriptor/layout/stride facts and `CertData` joins. Keep the extracted writer outputs as the authoritative ones. No new crypto trust; cache correctness/lifetime become native obligations. | L1 failure/retry behaviour preserved. L2 removal of duplicate challenge-derived traces requires simulator transport, not merely output equality. L3 re-pin optimized native binary and allocation/codegen evidence. |
| 4 | **Structure-aware emission and reuse within one attempt**: specialize repeated source rows, share bases or improve tagged elimination without changing its result. On the ~12 s emitter budget, a hypothetical 2–3× improvement saves **6–8 s**. This is not measured and overlaps row 1's emitter budget. | Certificate bytes may differ internally, but proof bytes stay identical only with equal accept/reject decisions. Broadening/narrowing the emitter's success set changes P_chk/retry law even if every returned certificate is valid: flag for lead/user review, not assumed harmless. | The untrusted emitter still requires the unchanged exact extracted checker. New source/certificate descriptors need valid builder bindings and malformed-input gates; no assumption that successful fixtures prove equivalence. | L1 predicate/retry law is critical. L2 pivots and early exits are challenge-derived, jointly simulatable under D166. L3 compiler/hardware evidence for new kernels; no silent return to stage-3 padding. |
| 5 | **Equivalent semantic sumcheck/claim evaluation and encoding algorithms.** Semantic sumcheck ~2.5 s (mostly ~2.1 s point claims); a hypothetical 2–4× improvement saves **1.2–1.9 s**. All commitment/folded encoding adds only ~1.1 s; 2× saves ~0.55 s. These cannot close the gap alone. | Same polynomial evaluations, coefficients, round messages and evaluation indices can preserve bytes. Changing arity, round count, field or code domain changes protocol/proof bytes and requires user approval and verifier/soundness work. | Rebind `host_sumcheck`, `host_semantic::point_claims`, `EncodingDomain::{evaluate,encode}`, coefficient permutation/weights and relevant part-47/48 semantic/opening joins. Unchanged witness CT arithmetic stays pinned. | L1 same output/errors. L2 new access/reduction schedule must retain the secret CT or challenge-simulation distinction. L3 compiler/SIMD audit and timing evidence renewed. |
| 6 | **Parallel Merkle, leaf hashing and salt derivation; SIMD/hardware SHA-256.** Combined salts+leaf assembly/hashing+parents is only ~0.6 s; even eliminating it has a **<0.7 s** ceiling here, and 4× projects ~0.45 s saving. SHA instructions are already present in the measured binary; this is not a missing 20-second SHA acceleration. | Same indexed salts, leaf grammar, ordered children, domains and digest backend preserve bytes. Changing hash/tree/leaf count requires approval and a new protocol/verifier/soundness argument. | Rebind salt-helper and Merkle step/loop callers and the selected digest contract. Parallel/hash-hoisting changes physical ROM query history: retain causal/order evidence or prove adaptive-oracle transport even if roots match. More workers also affect D133. | L1 preserve errors and nonce freshness. L2 independent indexed tasks still need a joint simulatable trace and safe secret handling. L3 SHA/vector dispatch and shared-cache/scheduling trust; new evidence, no CT conclusion from throughput. |
| 7 | **Allocation reuse**, especially scratch matrices and encoding workspaces. No allocator profiler was run, so **no positive saving is established**. The entire encoder is ~1.1 s; allocation-only savings there cannot exceed that, and a practical fraction is unknown. Checker allocation is inside its measured stages and cannot be added as another disjoint budget. | Same initialized outputs and failure semantics can preserve bytes; do not suppress allocation/shape errors or retain stale state. No verifier/protocol change for equivalent buffers. | Rebind buffer initialization, indexing, lifetime, capacity and drop/zeroization behaviour. Preserve secret salt wiping and durable nonce state. Allocator remains an explicit std trust boundary. | L1 history-dependent allocation failure observable; L2 capacity/initialization patterns must be simulatable. L3 allocator/cache effects and zeroization/codegen evidence renewed. |
| 8 | **Avoid repeated work across retry attempts.** All measured calls used one attempt, so **zero observed retry work to remove**. A cached public encoding domain saves at most its ~0.03–0.04 s per avoided rebuild (≤~0.25 s for seven extra attempts); immutable geometry/transport reuse has an unisolated additional budget. | Reuse only public invariant data. Fresh masks, salts, nonce reservations, masked commitments and challenge-dependent P_R1 work cannot be reused across distinct attempts by assumption. Skipping/reordering candidates can change published bytes/retry law; flag approval if semantics differ. | Rebind cache key/context, fresh-attempt and durable-ledger invariants and retry/L1 joins. Do not reuse random seeds or delete task keys. | L1 retries/reservations/errors are directly observable. L2 cache hit/miss/size history needs the same simulator treatment. L3 lifetime/cache evidence renewed; no new threading needed for public caches. |

**Recommended next deliverable, if separately authorized:** a byte-preserving P_R1-only design and scoped microprofile of builder families, emitter elimination and checker products, targeting ≥4× subsystem acceleration through exact blocked arithmetic, bounded workers and removal of duplicate column construction. Measure each adopted step against the D168 +10% stop gate. This report makes that recommendation concrete but does not begin implementation or approve any trust/protocol change.

## Validation and commit stages

Stage 1 commits: `328ae3d547` (scope/pins) and `d0c28ce8e7` (scratch profiler and capped runner). Stage 2 commit `9880fd61a4` records the raw primary/supplemental receipts, source/native pins, scratch diffs, operation counts, checked summaries and reproduction tools. `validation.json` checks twenty primary and four supplemental proofs and nine successful capped build/run receipts. Stage 3 is this final analysis/report. `ancestry-through-measurements.txt` records `git log --oneline f458169f7..9880fd61a4`; its inherited upstream commits are not work performed by this task. Only the report, evidence and task tools differ from the task base; no local target directory was created.

## Handoff and stop

Established by measurement: the repeated fixture latencies, spread, per-phase timings, one-attempt outcomes and strict/dense verification recorded above. Established by source inspection: the three full-size salted trees and exact hash-count formulas, duplicated source-column construction, serial long-running P_R1 loops and existing short scoped worker groups. Proposed only: all speedup multipliers, cache/algorithm changes and any under-15 projection.

No cryptographic, Lean or Kani assumption was discharged or added in this task. No implementation, wire format, acceptance predicate, verifier artifact or shipped source was changed. Existing security/refinement assumptions are retained; the current P_R1 threading/TLS boundary needs explicit scoping, and proposed workers need their own native refinement and trust assessment. Earlier v2 deterministic byte/ELF identity gates are context from D167, not rerun or attributed to these scratch binaries. No new claim of whole-prover security or L3 constant-time behaviour is made.

**Remaining blocker:** the measured P_R1 subtotal alone exceeds the latency target by more than a factor of two. A byte-preserving design must accelerate the complete subtotal by more than approximately 3.1× with the rest held fixed, and should target 4× for margin. The next concrete deliverable is the P_R1-only optimization design and focused product/emitter/builder profile described above, followed by separately authorized implementation and its equivalence, side-channel, artifact and performance gates. Retry-tail latency remains unmeasured. Any protocol/proof-byte/predicate change must be flagged to the user for approval. This job stops after analysis; nothing is pushed.
