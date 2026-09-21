# R17 candidate CU measurement

The 1,047,041 CU baseline replay is NOT a repair measurement. The requested
measurement concerns AV8/R17/structuredG271-two-channel/research-v1, including
its changed encoding, structured G and two quotient channels / Final512.
Privacy and soundness preservation remain open regardless of a CU result.

Latest boundary (R28): the primary deferred SBF pass accepts the retained
honest proof at its terminal checkpoint (24,208,293 diagnostic CU consumed).
The unchanged second reference pass then exhausts heap. The full program
still fails, both 1.2M/1.4M budgets fail, and no deployability/privacy claim
follows. Detailed chronological evidence, including regressions, is below.

## SBF preparation, 2026-09-21

Base privacy branch revision e7c9cffb plus this changeset. New
stage_r17_sbf_probe.py reconstructs the authenticated host candidate and appends
a read-only three-account entrypoint. It uses the candidate callback as the
crate root, preserving all verifier checks, including deferred/dense double
verification. It is verifier-only, not a Pool settlement adapter. Historical
missing complete-adapter preimages are not substituted or declared recovered.

The first bounded SBF build reached the actual candidate and failed with E0432:
the basis constructor imports two inventory functions excluded on Solana.
Exact log: evidence/r17-candidate-sbf-build-r1.log. Exit 1, wall 44.36 s,
peak process RSS 619,008 KiB, swaps 0; observed cgroup peak at least
1,436,512,256 bytes. Scope aspis-r17-sbf-probe-build-r1 used MemoryHigh=5G,
MemoryMax=7G, MemorySwapMax=0, TasksMax=128. Optimized cargo-build-sbf 2.3.0,
platform-tools v1.54; no full CU or accepted repaired execution resulted.

The retained host constructor was then executed by a new optimized exporter.
It checks that the 1,024-entry order is a permutation and emits all order and
inactive entries. Scope aspis-r17-export-basis-r3 used 4G/6G/zero-swap limits,
TasksMax=128. Exit 0, wall 26.39 s including compilation, peak process RSS
529,684 KiB, swaps 0; observed cgroup peak 1,025,425,408 bytes. Output is in
/home/dombarker/project-offloads/aspis-r17-sbf-probe-20260921-r3/basis-tables.rs.

install_r17_sbf_basis.py creates a fresh stage with an SBF-only table constructor;
the original host constructor remains intact. The build runner compares every
emitted byte from that host constructor to the installed constants before
attempting SBF compilation. This is a fixed source-data equality gate, not a
new hiding assumption or a general compiler-correctness theorem.

NUC access now uses the Tailscale address 100.108.41.90 as requested. After the
interruption, SSH confirmed only init.scope active and the old build terminal
with exit 1; no running build was restarted.

## Specialized-map build result

Fresh stage r5's optimized host equality gate PASSED: every order and inactive
entry matches the original constructor. SBF then compiled and emitted an ELF,
but reported a 4,736-byte frame in r17_opening_weights::original_weights,
640 bytes above the 4,096-byte maximum. The compiler returned 0; this is NOT
an accepted build. The runner now explicitly rejects such frame diagnostics.
No execution or CU acceptance was inferred from the produced ELF.

Scope aspis-r17-sbf-probe-build-r5 used 5G/7G/zero-swap, TasksMax=128.
SBF subprocess exit 0 with frame diagnostic, wall 34.54 s, peak process RSS
618,716 KiB, swaps 0. Observed aggregate scope peak 951,132,160 bytes before
completion. This timing excludes the preceding host equality compilation.
Exact log: evidence/r17-candidate-sbf-build-r5.log. Source/runtime changes only;
no Lean target changed, so no axioms audit applies to this build.

Immediate next implementation: route SBF mask weights through the retained
caller-buffer candidate, acquiring its coin/output buffers on the heap without
first constructing a large stack array, and preserve host differential controls.
The original mask function's 271-element QM31 array is 4,336 bytes before other
locals; its repeated mixing-row allocations also remain unsuitable for the
bump allocator. Source equivalence and allocation/publication obligations remain
explicit. A focused local SVM driver is prepared but not yet compiled or run.

## Heap-backed mask adapter and first loader test

Base 398c3f41 plus this changeset. install_r17_sbf_workspace.py creates a fresh
stage using the retained allocation-free mask_weights_into body unchanged.
Its adapter allocates two Vec buffers (271 and 1,024 QM31 values) directly on
the heap and borrows them as arrays; it does not construct either array on the
stack. The old mask routine remains as a host reference. It replaces neither
the mask formula nor verifier checks. Universal arithmetic/source equivalence
and allocation/failure privacy are still unproved; this is implementation work.

The initial cargo-test harness failed on unrelated imported prover unit tests
requiring HOST_HASH (exit 101, 27.81 s, RSS 534,588 KiB). A standalone --test
attempt still imported unrelated module unit tests (exit 1, 0.22 s, RSS 152,948
KiB). Final gate compiles the exact field, mask, and workspace modules as an
optimized standalone executable, with a direct 16-case adapter/reference check.
Compile exit 0, 0.41 s, RSS 142,056 KiB; run exit 0, 0.14 s, RSS 1,760 KiB.
Every one of the 1,024 outputs matched on all 16 points. No finite test is claimed
as a universal proof. All attempts had zero swaps, 4G/6G/zero-swap scopes,
TasksMax=128. Exact failed and successful logs are retained in evidence/r17-adapter-*.

R6 SBF build PASSED with no frame diagnostic: SBF subprocess exit 0, 34.51 s,
RSS 619,472 KiB, zero swaps; scope aspis-r17-sbf-probe-build-r6, 5G/7G/zero-swap,
TasksMax=128. The source-table equality gate also passed. Local simulator driver
build exit 0, 1.05 s, RSS 234,752 KiB, zero swaps, scope aspis-r17-svm-build-r6,
4G/6G/zero-swap, TasksMax=128.

The actual R17 proof fixture was attempted, but ELF loading failed BEFORE
execution: `.bss._ZN24aspis_` section/symbol name rejection. Run exit 2, 0.01 s,
RSS 17,252 KiB, zero swaps, scope aspis-r17-svm-run-r6, 3G/4G/zero-swap,
TasksMax=64. Therefore no repaired CU number or runtime acceptance was obtained.
The diagnostic points to the host-style OnceLock map cache. A fresh R7 stage
replaces only SBF storage with immutable read-only arrays, retaining the host
constructor and the complete map equality gate; no dynamic map cache is needed.

## Actual repair candidate execution: CU failure

The immutable-map R7 build passes both the source equality gate and SBF
frame checks. SBF subprocess exit 0, wall 34.54 s, peak process RSS 618,612
KiB, swaps 0; 5G/7G/zero-swap scope aspis-r17-sbf-probe-build-r7,
TasksMax=128. The ELF loads successfully in the local simulator.

| R17 verifier-only case | Limit | Result |
| --- | ---: | --- |
| Honest retained world0 proof | 1,200,000 | CU exhaustion |
| Honest retained world0 proof | 1,400,000 | CU exhaustion |
| Honest retained world0 proof | 100,000,000 (diagnostic) | CU exhaustion |
| Corrupted G final value | same three limits | CU exhaustion at each |

There is NO successful verification or total-completion CU measurement.
The corrupted cases are not checked negative rejections: they also exhaust
resources. The simulator reports ProgramFailedToComplete and explicitly logs
"exceeded CUs meter at BPF instruction". All supplied accounts remain unchanged.
This is the actual R17 candidate, not the old baseline. It currently does not
fit even the verifier-only budget; no deployability or complete-transaction
claim is made. The retained dense-reference cross-check is still present.

ELF SHA256: 561b730b38ef71f0216331a447930894142ef42e328bcf340956b440b729168a.
Proof SHA256: a9d851aeeb68193c00791beeae2cbcd0aa894b1ae51e9f051c64020063612fb5.
Driver SHA256: 34d87c8d4d5cb9b850e22342328ec9cc25e9f36435d982f47c69315ea9dbc2b4.
Exact evidence: evidence/r17-candidate-svm-run-r7.jsonl and .log;
build evidence: evidence/r17-candidate-sbf-build-r7.log. Scope
aspis-r17-svm-run-r7 used 3G/4G/zero-swap, TasksMax=64; wall 0.20 s,
peak RSS 26,372 KiB, swaps 0. Driver exit 0 means all six observations were
recorded with no corruption acceptance; it DOES NOT mean the candidate passed.

Next: instrument named candidate stages to locate the cost before changing
the algorithm. Do not rerun unchanged at a larger diagnostic limit. In
particular, the direct 271-by-1024 mask expansion is a source-visible candidate
for investigation, not yet an isolated measured attribution. Preserve its
functional constraints if replacing it with a faster evaluation method.
Then address heap/CU limits without dropping checks and measure the integrated
complete transaction. No deployment, external transaction or wallet operation
occurred; no global privacy or soundness obligation was declared closed.

## R8 stage attribution, same budgets

Base 769dce0b plus this changeset. stage_r17_cu_profile.py creates a fresh
copy of the candidate and inserts fixed public stage labels and remaining-CU
syscalls. No witness values are logged. Verifier checks, transcript absorption,
mask construction, and double verification remain unchanged. The build runner
checks both pre-instrumentation hashes and resulting source hashes. These
instrumented deltas include marker overhead and are not quiet-build CU totals.

On the honest fixture at the same 100M diagnostic limit:

| Interval | Remaining before | Remaining after | Instrumented delta |
| --- | ---: | ---: | ---: |
| Semantic verification | 99,948,085 | 99,215,212 | 732,873 |
| First-channel original weights | 99,098,363 | 78,738,778 | 20,359,585 |
| First-channel basis dual | 78,738,778 | 78,658,744 | 80,034 |
| First-channel chord transpose | 78,658,744 | 76,383,448 | 2,275,296 |
| Structured-channel original weights | 76,383,234 | exhaustion | incomplete |

At 1.2M and 1.4M, execution exhausts inside first-channel original_weights.
At 100M it reaches the second original_weights call and exhausts there before
the original-end marker. Thus there is no complete verification at any tested
budget. Corruption controls likewise exhaust; they are not checked rejections.
The second interval includes the whole structured original-weight construction,
not an isolated mask-only measurement. Do not attribute its entire cost to G
without finer evidence. The two channels' dense construction is now a measured
bottleneck, rather than an inference from code size.

Source inspection: WeightAccumulator::weight_at multiplies all ten multilinear
factors independently per coordinate. original_weights calls it 1,024 times
for three point components (two for the structured channel), repeating prefix
products. The next exact-preserving candidate is a shared-prefix tensor
expansion, checked against this retained source. The 271-by-1024 G map needs
separate optimization; dropping or replacing its constraints is not permitted.

SBF build: scope aspis-r17-sbf-profile-r8, 5G/7G/zero-swap, TasksMax=128,
exit 0, 34.42 s, peak process RSS 622,116 KiB, swaps 0; source equality and
frame checks pass. Runtime: scope aspis-r17-svm-profile-r8, 3G/4G/zero-swap,
TasksMax=64, driver exit 0, 0.19 s, RSS 26,280 KiB, swaps 0. Driver exit 0
again means observations recorded, NOT candidate acceptance. Exact logs are
evidence/r17-candidate-sbf-profile-r8.log and
evidence/r17-candidate-svm-profile-r8.{jsonl,log}. Proof/driver unchanged from
R7. No larger budget or unchanged quiet replay was run. No formal-security
gate closes from this profile; the goal remains incomplete.

## R10 shared-prefix tensor implementation

Base 139daff0 plus this changeset. r17_tensor_prefix.rs expands each existing
multilinear tensor by shared prefixes. Each leaf retains exactly the old
left-associated multiplication order; no division, reassociation, or zero
exception is introduced. Descending parent indices prevent writes from
overwriting unread parents. At level d the first 2^d slots hold that level's
prefix products; each slot is initialized before use. Ten levels produce
the same big-endian 1,024 leaves. This is the intended loop invariant, not
yet a compiled source-refinement theorem.

stage_r17_tensor_prefix.py uses a fresh research stage and preserves the old
original_weights_reference on host. Contributions are added in the same point
order, followed by the same inactive-row constant and the same G contribution.
No source pins are waived: the runner authenticates the before/after chain,
including the earlier workspace adapter and the unchanged instrumentation.
The new scratch buffer adds 16 KiB of allocation per original_weights call;
its effect on complete bump-heap usage remains open.

Optimized actual-source gates passed:

- 20 cases x 1,024 leaves match the actual core WeightAccumulator::weight_at,
  including zero, one, P-1 points, zero scale and extension-field coordinates.
- Six cases x both channels x 1,024 complete weights match the retained
  original_weights reference, including inactive constants and G weights.

These are finite differential tests, not a universal privacy/correctness proof.
Host gate scope aspis-r17-tensor-gate-r10, 4G/6G/zero-swap, TasksMax=128:
exit 0, wall 25.93 s including compilation, peak process RSS 531,196 KiB,
swaps 0. SBF source equality/frame gate passes: scope aspis-r17-tensor-sbf-r10,
5G/7G/zero-swap, TasksMax=128, exit 0, 34.67 s, RSS 619,372 KiB, swaps 0.
No Lean file changed, so no new axioms audit applies.

Same-fixture instrumented first-channel original_weights cost is now
99,098,363 - 95,459,915 = **3,638,448 CU**, versus 20,359,585 in R8,
saving 16,721,137 CU (about 82%). Basis dual and chord stages remain
80,034 and 2,275,296 respectively. The second original_weights stage starts
with 93,104,371 CU remaining and still exhausts the diagnostic budget.
All six honest/corruption observations remain resource failures; no accepted
proof or successful corruption-rejection endpoint was obtained. The limits
are unchanged at 1.2M, 1.4M and diagnostic 100M.

Runtime scope aspis-r17-tensor-svm-r10, 3G/4G/zero-swap, TasksMax=64:
driver exit 0 (observations only), 0.18 s, RSS 26,716 KiB, swaps 0.
ELF SHA256 67a4515db97223234c737952afeb3d645a534b666d1f5053bdc04d479b178342.
Exact evidence: evidence/r17-tensor-gate-r10.log, r17-tensor-sbf-r10.log,
r17-tensor-svm-r10.{jsonl,log}. Host stage r9 was a preliminary unbuilt draft;
r10 includes the complete-channel differential gate. Neither is a new security
profile: the mathematical weights and transcript inputs are unchanged.

Remaining performance obligation: reduce the structured-G construction cost
and further reduce ordinary/chord costs to the real budget, with corresponding
source-correctness evidence. Full transcript privacy and soundness preservation
remain open; this measured optimization does not close them.

## R11 base-field powers: reaches the heap boundary

Base 554be246 plus this changeset. stage_r17_base_powers.py creates a fresh
stage, preserving the original pinned workspace source and all old stages.
Nodes remain exactly 1..271; coin construction, output ordering and sum order
are unchanged. Only the power recurrence uses M31 instead of its QM31 embedding,
and each coefficient is scaled with mul_m31. No mask resampling, new map or
hiding assumption is introduced. The intended arithmetic bridge is embedding
compatibility for canonical M31 powers and QM31 scalar multiplication; it is
not yet a compiled actual-source correspondence theorem.

Optimized gates passed: 20 tensor cases x 1,024 entries; six G cases x 1,024
entries versus the retained full-QM31-power mask implementation; six complete
original-weight cases x both channels x 1,024 entries. This finite evidence does
not prove universal correctness/privacy. Scope aspis-r17-base-gate-r11,
4G/6G/zero-swap, TasksMax=128: exit 0, 26.01 s including compilation,
peak process RSS 530,124 KiB, swaps 0. SBF source/table/frame checks pass;
scope aspis-r17-base-sbf-r11, 5G/7G/zero-swap, TasksMax=128: exit 0,
34.52 s, RSS 618,484 KiB, swaps 0. No Lean declaration changed.

Actual same-fixture SVM execution at unchanged limits:

- 1.2M and 1.4M: still CU exhaustion, not accepted.
- Diagnostic 100M: structured original_weights completes. Its instrumented
  interval is 93,104,371 - 60,088,726 = **33,015,645 CU**. This includes the
  whole structured original-weight construction, not G alone.
- Immediately afterwards, before the structured dual-end marker, the runtime
  logs "memory allocation failed, out of memory" and "SBF program panicked".
  The observed total is **39,911,418 CU to failure**, NOT total verification CU.
  Honest and corrupted cases fail identically; no checked negative endpoint.

Scope aspis-r17-base-svm-r11, 3G/4G/zero-swap, TasksMax=64: driver exit 0
(observations only), 0.13 s, RSS 26,644 KiB, swaps 0. Simulator heap remains
256 KiB. No host cgroup OOM occurred and neither heap nor CU limit was raised.
ELF SHA256 6da823a798a70baad1b3de42404e8e3fcf54a15cdeeeb5b6feda6f5afff94ebc.
Exact evidence: evidence/r17-base-gate-r11.log, r17-base-sbf-r11.log,
r17-base-svm-r11.{jsonl,log}. The proof and driver are unchanged from R7.

Next source implementation obligation is allocation reuse across original
weights, basis dual and chord transpose. The present chord path alone clones
and grows its input and materializes five intermediate vectors before its
output; dropped Vec allocations are not reclaimed by the SBF bump allocator.
The observed allocation failure is between the second original-end and dual-end
markers. Optimize ownership/scratch reuse without changing the fixed map or
checks, then remeasure. Even after resolving this heap failure, the measured
33M weight stage is far above the deployable budget and needs a substantially
cheaper evaluation route. Full privacy and soundness preservation remain open.

## R12 owned dual/chord: preparation completes

Base 76be8af5 plus this changeset. r17_owned_weights.rs consumes the existing
weight Vec rather than allocating fresh dual/chord output vectors. It first
applies the same inactive-coordinate pivot subtraction, then gathers by the
source-checked permutation using cycle rotation and a 1,024-byte visited array.
Permutation validity remains checked by the retained host map gate. The chord
routine reads zero-padded even/odd projections directly, materializes only
xwa/xxwa/xwb, and writes each output pair into the original Vec after reading
that pair. Arithmetic expressions/order remain those of the reference. No
unsafe code, field assumption, map change, or dropped verifier check is added.
The actual loop/source correspondence is not yet a compiled Lean theorem.

Focused optimized tests pass: 20 cases x 1,024 dual and chord entries equal the
retained references. The tensor, G, and complete-weight differential controls
also pass. Stage_r17_owned_weights.py preserves before/after hashes and old
reference functions. Runner verifies this new hash chain through the prior
tensor and instrumentation stages. The change is isolated to research staging.

Scopes/measurements, all zero swaps and TasksMax=128 except runtime=64:

| Target / scope | Limits high/max/swap | Exit | Wall s | Peak RSS KiB |
| --- | --- | ---: | ---: | ---: |
| optimized gate / aspis-r17-owned-gate-r12 | 4G/6G/0 | 0 | 26.75 | 528576 |
| SBF build / aspis-r17-owned-sbf-r12 | 5G/7G/0 | 0 | 34.56 | 619204 |
| simulator / aspis-r17-owned-svm-r12 | 3G/4G/0 | 0 | 0.13 | 26364 |

SBF source/table/frame checks pass. No Lean target changed. Runtime exit 0
again means observations recorded, not successful proof verification.
At diagnostic 100M, both original-weight/dual/chord stages now complete and
the first prepare-end marker is reached with 57,636,780 CU remaining.
The program then logs out-of-memory and panics at **42,363,431 CU to failure**.
This later failure is progress past R11's preparation failure, not a full heap
fix or a completed verification. Honest and corrupt cases both fail, and the
1.2M/1.4M cases still exhaust CU. No heap/CU limit was increased.

ELF SHA256 c38e36a1619474c9bb581143c9129b0d08cb7136864408763597197aae74a986.
Exact evidence: evidence/r17-owned-gate-r12.log, r17-owned-sbf-r12.log,
r17-owned-svm-r12.{jsonl,log}; fixture/driver unchanged. Source inspection
identifies the next immediate allocation: r17_host_relation::verify constructs
two dense 1,024-coordinate reference vectors unconditionally, even when
reference=false. Only the reference branch consumes those vectors. Next is
conditional construction while retaining both verification paths and their
agreement check. Further heap and major CU work remains, as do all outstanding
full-transcript privacy, source-refinement and soundness obligations.

## R13 reference-only dense allocation; actual host proof accepted

Base 3c25e412 plus this changeset. stage_r17_lazy_reference.py allocates the
two dense vectors only when reference=true. For reference=false they are empty
and remain unused. Both verifier passes, their equality assertion, transcript,
query schedule and opening checks remain. Fixed diagnostic markers were added
after dense initialization, after first folding, after query scheduling and
after openings. Source hashes are checked through the full prior edit chain.

The actual retained world0 R17 proof is accepted by the updated host binary,
which executes both paths and asserts their outcome agreement. A separate copy
with byte 697*16 flipped is rejected. The historical reject-existing entrypoint
prints R17_LEGACY_PROFILE_REJECTED for any rejected fixture; in this gate the
fixture is explicitly a current-profile G-final corruption, not a legacy proof.
Neither negative nor positive host result is an SBF result or global-security
proof. Test copies contain public fixtures only; no keys are created or removed.

Scope aspis-r17-lazy-host-r13: 4G/6G/zero-swap, TasksMax=128. Positive run
including optimized compilation: exit 0, 35.06 s, RSS 537,356 KiB, swaps 0.
Negative run: exit 0, 0.00 s reported, RSS 3,168 KiB, swaps 0. Exact source and
commands are in tools/check_r17_host_proof.py and evidence/r17-lazy-host-r13.log.

SBF source/table/frame gates pass. Scope aspis-r17-lazy-sbf-r13:
5G/7G/zero-swap, TasksMax=128, exit 0, 34.59 s, RSS 618,780 KiB, swaps 0.
At 100M diagnostic CU, the actual SBF run reaches prepare-end and dense-ready,
then runs out of heap before first-fold-end, at **42,370,028 CU to failure**.
This does not isolate the exact failing allocation among transcript/fold work
in that interval. No SBF proof acceptance or checked malformed-proof rejection
is observed. The 1.2M/1.4M cases still exhaust CU. The heap stays 256 KiB.

Scope aspis-r17-lazy-svm-r13: 3G/4G/zero-swap, TasksMax=64, driver exit 0
(observations only), 0.13 s, RSS 26,292 KiB, swaps 0. ELF SHA256:
dadc4791399e4ed4b77ddd8e5a49d5716c67a47eb324495b95f35b7448366e10.
Exact build/runtime evidence: evidence/r17-lazy-sbf-r13.log and
evidence/r17-lazy-svm-r13.{jsonl,log}; proof and SVM driver unchanged.

Next source ownership fix: prepare currently clones both ordinary vectors
into the weight accumulators even though ordinary is not needed afterwards.
Move those vectors into the accumulators instead of allocating two new buffers.
The broader fixed-heap lifetime budget and excessive CU remain unresolved.
No Lean theorem changed; no source-refinement, privacy or soundness gate closes.

## R14 consumed preparation vectors

Base e32bac9b plus this changeset. stage_r17_move_prepared.py moves both
ordinary vectors into their accumulators instead of cloning them, avoiding
32 KiB of duplicate coefficient buffers. Both verifier paths remain intact.
Actual host proof: accepted; modified current G-final: rejected (both exit 0).
Host scope 4G/6G/zero swap: positive 35.15 s, peak RSS 532316 KiB;
negative 0.00 s reported, 3344 KiB; both zero swaps.
SBF source/table/frame gates pass: exit 0, 34.77 s, 619020 KiB, zero swaps,
scope 5G/7G/zero swap. Source revision is e32bac9b plus staged R14 changes.

SVM scope 3G/4G/zero swap: observation driver exit 0, 0.14 s,
26384 KiB, zero swaps. Honest/corrupt still exhaust 1.2M and 1.4M CU.
At diagnostic 100M, both now reach first-fold-end and query-schedule-end,
then fail allocation before openings-end: honest 44341797 CU to failure,
corrupt 44341224. These are not complete verification costs or a checked
negative rejection. Heap remains 256 KiB; no limit was raised.
ELF SHA256 cab8442e4acd54450cf9434acf432352d7426dc85cf33a5746acb45e3c7fa62c.
Evidence: r17-move-host-r14.log, r17-move-sbf-r14.log,
r17-move-svm-r14.{jsonl,log}. No Lean target changed; axioms audit not applicable
to this Rust ownership change. Formal source refinement remains open.

Structural optimization priority: retain sparse/structured weights and exploit
aligned bases. The present source absorbs both expanded ordinary weight arrays
into the transcript, so simply omitting expansion changes that transcript.
Any such new profile needs explicit chronology and soundness/privacy arguments.
An exact-preserving intermediate experiment precomputes the fixed G Vandermonde
powers and batches four base-field products per reduction. It does not change
the encoding, pads, challenges or transcript values. Finite equality tests are
not its universal source-refinement proof, nor a full privacy theorem.

## R15 fixed G powers and bounded four-product accumulation

Base e32bac9b plus R14 and this changeset. stage_r17_fixed_g_table.py emits
the same 277504 base-field powers in output-major read-only storage. Four
canonical products per component are accumulated in u64, reduced, then added
to the running M31 sum. The bound is 4*(2147483646)^2 < 2^64. The last block
has three terms. Coin construction, output ordering and mathematical values
are unchanged; arithmetic association changes. This remains a dense map.

Focused optimized host gate checks every table entry against source M31
power recurrence, the maximal four-product reduction, 20 owned-dual/chord
cases, 20 tensor cases, six complete G maps and six pairs of complete opening
weight maps against retained references. Actual host proof is accepted and
current G-final corruption rejected; both verifier paths remain enabled.
Scope 4G/6G/zero swap: focused gate exit 0, 27.62 s, RSS 533876 KiB;
positive proof exit 0, 9.26 s, 404072 KiB; negative exit 0, 0.00 s reported,
4400 KiB. All zero swaps. Source/table/frame SBF checks pass: exit 0,
35.15 s, RSS 619400 KiB, zero swaps, scope 5G/7G/zero swap.

Actual repaired-candidate SVM at the same diagnostic 100M budget reduces
the second original-weight stage from 33015646 to **26650460 CU** (19.28%).
The honest execution still runs out of heap after query-schedule-end at
37976611 CU to failure; the corrupt execution at 37976038. Neither completes
verification. Both 1.2M/1.4M pairs still exhaust CU. Heap stays 256 KiB.
This is a stage improvement, not a completed verifier CU figure.
Observation driver exit 0, 0.15 s, RSS 31712 KiB, zero swaps,
scope 3G/4G/zero swap. ELF SHA256:
3c9bd9cd9e2c219f54d3d4e52ecd9d6229616002634e038e84ba232546bcc62a.
Exact evidence: r17-fixed-g-host-r15.log, r17-fixed-g-sbf-r15.log,
r17-fixed-g-svm-r15.{jsonl,log}. Source revision e32bac9b plus the generators
and builder recorded in this changeset; fixture and driver unchanged.

No Lean target changed or new theorem compiled; #print axioms is not
applicable to these Rust gates. Canonicality/overflow and reassociated-sum
source refinement remain proof obligations. Full privacy and soundness
remain open. R17_STRUCTURAL_CU_PLAN.md records the exact generating-function
route to remove the dense multiplication, and the constraints on sparse
mixing/aligned bases and the current transcript absorption.

## R16 exact-map tree and extension-field convolution prototype

Source base 0e8af97d plus this changeset. tools/r17_fast_g.rs implements
the generating-function route in R17_STRUCTURAL_CU_PLAN.md. Its numerator
uses a fixed denominator product tree (schoolbook merges for now); final
multiplication by the truncated inverse denominator uses a 2048-point CM31
transform. This changes no source nodes, coins, mathematical weights, basis,
transcript bytes or proof format. It introduces no challenge denominator.
The CM31 root is the retained source circle generator (2,1268011823) raised
to 2^20; exact order 2048 is checked, not assumed from M31 roots of unity.
The convolution degree is at most 270+1023=1293 < 2048, so there is no
cyclic aliasing in this embedding. The inverse normalization is 2^20 in M31.

Optimized Rust generates the fixed denominators, root powers and inverse
spectrum in a 4G/6G/zero-swap scope. Most generation-command time is cached
crate compilation, not the small fixed-polynomial generation step. Exit 0,
26.38 s, peak RSS 534848 KiB, zero swaps. The generated table hash and kernel
hashes are enforced by the source-pinned SBF builder; no pin is waived.

Focused optimized gate checks exact root order and all powers, FFT roundtrip,
the highest numerator basis impulse convolution, every coefficient of
D * inverse(D) = 1 modulo X^1024, and six arbitrary coin maps (including
maximal canonical limbs and the first/last basis edges) against direct
power sums. Prior 20-case tensor/owned-dual/chord controls, six full G maps,
and six pairs of complete opening-weight maps still pass. The actual host
proof is accepted and G-final corruption rejected, with both verifier paths
and the equality assertion retained. No negative regression was removed.

4G/6G/zero-swap host scope: focused gate exit 0, 1.67 s, 286884 KiB;
positive exit 0, 9.38 s, 427260 KiB; negative exit 0, 0.00 s reported,
3344 KiB. All zero swaps. 5G/7G/zero-swap SBF scope: source/table/frame gates
pass, exit 0, 35.42 s, 621220 KiB, zero swaps.

Actual SBF second original-weight stage: **24536806 CU**, versus R15's
26650460 (7.93% lower). It is not the whole verifier cost. The extra
workspace worsens the heap endpoint: at diagnostic 100M, honest and corrupt
both fail allocation at 34862199 CU, after first-fold-end but before
query-schedule-end. R15 had reached query-schedule-end. This regression is
retained explicitly; no heap limit was raised (still 256 KiB). Both 1.2M and
1.4M pairs still exhaust CU. Neither honest acceptance nor checked negative
rejection occurs in SBF. Observation driver exit 0, 0.13 s, 26908 KiB,
zero swaps, scope 3G/4G/zero swap. ELF SHA256:
0d0df8402e48a8ab99f70410dd4f60e6060316ce2e95b92f527975e97b1f4cbe.

Evidence: r17-fast-g-generate-r16.log, r17-fast-g-host-r16.log,
r17-fast-g-sbf-r16.log, r17-fast-g-svm-r16.{jsonl,log}. All stages use the
same retained public proof and SVM driver. No deployment or wallet operation.

Next implementation targets: the numerator's 75548 scalar products still
use schoolbook merges; FFT workspace and both numerator buffers add heap
pressure. Profile/isolate these, specialize or accelerate the large merges,
and reuse workspace. The transform prototype is not yet a release replacement.
First remaining proof proposition: for every canonical source coin vector,
the concrete tree, transform, truncation and field implementation yield the
same 1024 canonical bytes as the retained power-sum map. No new Lean target
was compiled this turn; #print axioms is not applicable to the Rust gates.
Finite checks do not establish that universal refinement or full privacy.

## R17 reused G workspaces and batched numerator merges

Source base d18568cc plus this changeset. stage_r17_fast_g_reuse.py changes
only the research kernel and its opening-weight caller. It computes the
numerator using two disjoint 271-coordinate slices of the already allocated
1024-coordinate output. After the nine merge levels it places the numerator
in the first slice. The FFT copies all numerator c0 components before writing
output c0, and copies the untouched numerator c1 components before writing
output c1. No unsafe casts or allocator changes are used. The caller reuses
the consumed tensor scratch as G output. This avoids two 4336-byte numerator
allocations and a separate 16384-byte G output allocation (25056 bytes total).
The 16384-byte CM31 transform workspace remains allocated.

Each tree output now accumulates at most four canonical scalar products per
u64 component before reduction. The product set is unchanged; association
changes. Range endpoints explicitly select the two convolution diagonals.
The inherited bound 4*(2147483646)^2 < 2^64 applies, with all outputs reduced
before the next level. Field canonicality and source refinement are still
formal obligations, not inferred from successful tests.

The optimized host gate now additionally checks every one of the 271 coin
basis positions at every one of the 1024 outputs, using distinct nonzero
extension components (3,5,7,11) and reusing dirty output storage. All prior
root/inverse/convolution/reference controls pass. The actual retained proof
is accepted and the current G-final corruption rejected; both verifier paths
and their equality assertion remain. 4G/6G/zero-swap scope:
focused gate exit 0, 27.98 s including compilation, peak RSS 535184 KiB;
positive exit 0, 9.43 s, 427004 KiB; negative exit 0, 0.00 s reported,
3344 KiB. All zero swaps. The fixed polynomial tables are unchanged, so their
generator was not rerun. No Lean target changed or compiled; an axioms audit
is not applicable to these Rust gates. Full privacy is not established.

R17 SBF source/table/frame gates pass: exit 0, 35.38 s, peak RSS 619492 KiB,
zero swaps, scope 5G/7G/zero swap. Diagnostic second original-weight stage
is **25403570 CU**, worse than R16's 24536806 (3.53%). Fixed additional
markers isolate 8695076 CU from G-tree-start to G-tree-end and 13366564 CU
from G-tree-end to G-fft-end (including buffer setup, both components,
transforms, pointwise products, normalization, output copies and markers).
Do not call the latter an isolated butterfly cost.

The allocation change recovers the later endpoint: honest and corrupt reach
query-schedule-end and then run out of heap before openings-end, at 36753510
and 36752937 CU respectively. Both still exhaust 1.2M/1.4M CU. Heap remains
256 KiB. Driver exit 0 is observations only: 0.14 s, peak RSS 26796 KiB,
zero swaps, scope 3G/4G/zero swap. ELF SHA256:
d88d48c8bae926bc3f1c3dcabea3080ba588bb53fa94b2c6c713f19e518932db.
Evidence: r17-fast-g-reuse-host-r17.log, r17-fast-g-reuse-sbf-r17.log,
r17-fast-g-reuse-svm-r17.{jsonl,log}.

The batched-merge arithmetic experiment is rejected as a CU improvement;
retain its failure evidence. The next R18 stage restores original arithmetic
order but retains safe output/tensor buffer reuse, exhaustive basis checks
and the new attribution markers. It does not raise memory or CU limits.

## R18 retain allocation savings; restore original merge arithmetic

Same source base d18568cc plus the R17/R18 changeset. The restored merge
passes all focused controls including all 271 basis positions and dirty
output reuse. Actual host proof accepted and G-final mutation rejected.
Host 4G/6G/zero-swap scope: focused gate exit 0, 27.88 s, RSS 535588 KiB;
positive exit 0, 9.40 s, 426640 KiB; negative exit 0, 0.00 s reported,
3344 KiB. SBF source/table/frame gates pass: exit 0, 35.26 s, 619064 KiB,
5G/7G/zero-swap scope. All zero swaps.

Second original-weight stage is **24621207 CU**. G tree is 7909059 CU;
FFT section is 13370660 CU under the same marker definitions as R17.
The R17 batching regression is removed. R18 is slightly more CU than R16
(which had no inner markers), but has the 25056-byte allocation saving and
reaches query-schedule-end again. Honest/corrupt then run out of heap before
openings-end at 35971177/35970604 CU to failure. These are not completed
verification costs or checked negative rejections. Both still exhaust the
1.2M and 1.4M budgets. Heap remains 256 KiB; no limit was raised.

Observation driver exit 0, 0.12 s, RSS 26864 KiB, zero swaps,
scope 3G/4G/zero swap. ELF SHA256:
8e1f73c792051e15efde66200bd3c596769c1c55a993288a4ec8a842ddb20f43.
Exact evidence: r17-reuse-only-host-r18.log, r17-reuse-only-sbf-r18.log,
r17-reuse-only-svm-r18.{jsonl,log}. No Lean target compiled; universal
source arithmetic/refinement and full-transcript privacy remain open.
The next bounded optimization is a source-equivalent fused CM31 butterfly,
with independent overflow/equality checks before the full finite basis gate.
The existing sparse/aligned-basis and source-security obligations remain;
none is discharged by the performance evidence here.

## R19 fused CM31 butterflies and compiled arithmetic bounds

Base 97f50b92 plus this changeset. stage_r17_fused_fft.py replaces the
multiply-then-add/subtract butterfly with four canonical reductions of the
raw expressions recorded in R17_STRUCTURAL_CU_PLAN.md. A public index-zero
twiddle uses direct add/subtract. Inverse normalization uses the existing
M31.mul_pow2(20), with the same factor 2^20. No data-dependent zero skipping,
new rejection, sampled mask, transform ordering or transcript change occurs.

New optimized checks compare 15625 limb-boundary tuples with source CM31
operations, use checked u64 operations for each intermediate, and check
every one of the 2048 fixed roots plus normalization. All prior checks pass,
including 271 basis positions x 1024 outputs, unequal extension components,
dirty-buffer reuse, six arbitrary coin maps and full opening-weight maps.
The actual retained host proof is accepted; G-final corruption is rejected.
Both verifier paths and their equality assertion remain enabled.

Host 4G/6G/zero-swap scope: focused gate exit 0, 27.93 s, RSS 537672 KiB;
positive exit 0, 9.46 s, 428224 KiB; negative exit 0, 0.00 s reported,
3520 KiB. SBF source/table/frame gates pass: exit 0, 35.45 s,
621408 KiB, scope 5G/7G/zero swap. All task swaps are zero.

The measured FFT section falls from 13370660 to **8525873 CU** (36.23%).
The G tree remains 7909059 CU; the complete second original-weight stage
falls from 24621207 to **19776420 CU** (19.68%). These are marker intervals,
not a completed verifier cost. Honest/corrupt still run out of heap after
query-schedule-end, before openings-end, at 31126390/31125817 CU to failure.
Both 1.2M/1.4M pairs still exhaust CU. Heap stays 256 KiB. No SBF proof
acceptance or checked negative rejection was observed.
Observation driver exit 0, 0.13 s, RSS 26568 KiB, zero swaps,
scope 3G/4G/zero swap. ELF SHA256:
f4b1783c546fc985ae04dd254c1f7a64bb0079d66a6b44be0cb7f535d513ff4c.
Evidence: r17-fused-fft-host-r19.log, r17-fused-fft-sbf-r19.log,
r17-fused-fft-svm-r19.{jsonl,log}.

### Focused Lean boundary

AspisV8R17/FusedButterflyBounds.lean compiles using cached Lean 4.32.0 and
mathlib 81a5d257c8e410db227a6665ed08f64fea08e997, with lake env lean,
-j1 -M1600. It proves the canonical product bound, each subtraction's
non-underflow condition and addition/result bounds in the stated evaluation
order, and identifies the padding constant with P^2. It does not yet prove
that the Rust reducer returns those residues or that the entire FFT refines
the retained source map. Canonical-input premises must still be source-bound.

Scope 1G/2G/zero swap, TasksMax=64: exit 0, 1.51 s, peak RSS 1636136 KiB,
swaps 0. Source revision 97f50b92 plus this leaf and staged kernel changes.
#print axioms: canonical_product_bound uses propext and Quot.sound;
raw_bounds uses propext, Classical.choice and Quot.sound;
padding_is_prime_square uses propext. No sorryAx or user-added axiom.
The first launch failed before theorem checking because the input lay outside
Lake's default root (exit 1, 0.73 s, 818080 KiB, zero swaps); passing the
isolated stage explicitly as --root fixed the environment. Both logs retained:
r17-butterfly-bounds-root-failure-r19.log and r17-butterfly-bounds-r19.log.
Only this smallest changed leaf was compiled; no unchanged manifest replay.
The host had pre-existing swap usage; zero-swap scope limits and the listed
task swap counts do not assert that the entire host had no swap in use.

First remaining arithmetic proof step: connect canonical source operands and
the retained reducer refinement to these raw integer bounds and the four
field residues. Whole-transform source equivalence and all full-transcript
privacy, soundness, retry/publication and resource-failure obligations remain
separate. The performance improvement closes none of those broader gates.

## R20 scalar FMA and reused transcript serialization

Base b23f7594 plus this changeset. stage_r17_scalar_fma.py keeps the original
tree scatter order, replacing each QM31-by-M31 multiplication followed by
addition with one reduction of acc + x*y per M31 limb. It does not restore
the rejected four-product diagonal batching loop. The same stage reuses one
16384-byte weight serialization buffer across both channels. Every byte is
rewritten with the same source write_le_bytes method; labels, lengths, order
and absorption calls remain. A host-only assertion compares both encodings
with the original bytes(v) implementation. This avoids one 16 KiB SBF
allocation without omitting the expanded weights from the transcript.

125 boundary triples check the scalar FMA against source field operations,
with distinct extension limbs and checked u64 intermediates. All previous
butterfly, FFT, 271-basis-position, dirty-buffer and complete-weight controls
pass. The actual host proof is accepted and G-final corruption rejected;
both verifier paths and the independent combined-opening check remain.
Host scope 4G/6G/zero swap: focused exit 0, 28.08 s, RSS 533900 KiB;
positive exit 0, 9.44 s, 428012 KiB; negative exit 0, 0.00 s reported,
3344 KiB. SBF source/table/frame gates pass: exit 0, 35.46 s, 619036 KiB,
scope 5G/7G/zero swap. All task swap counts are zero.

G tree interval falls from 7909059 to **5455352 CU**; FFT remains 8525873.
Second original-weight interval falls from 19776420 to **17323740 CU**.
The honest diagnostic SBF execution now reaches opened-points,
opened-records, opened-authenticated and openings-end, including the retained
combined-opening reference check. It then exhausts heap at 29712455 CU,
after openings and before a completed verifier result. The corrupt execution
reaches opened-records, then starts the second semantic pass without an
opened-authenticated marker, and later exhausts heap at 29541974 CU. By source
control flow this is consistent with the first path returning authentication
error, but the overall SBF result is still resource failure, not a completed
checked rejection. Do not count it as a negative verifier pass.

Both 1.2M/1.4M pairs still exhaust CU. Heap stays 256 KiB; diagnostic 100M
budget is unchanged. Observation driver exit 0, 0.13 s, RSS 26624 KiB,
zero swaps, scope 3G/4G/zero swap. ELF SHA256:
29b9dbc16649ef19dc8c9d0118ac8846bce7459264dd1fd9b77c49ec870e8c92.
Evidence: r17-scalar-fma-host-r20.log, r17-scalar-fma-sbf-r20.log,
r17-scalar-fma-svm-r20.{jsonl,log}.

The changed FusedButterflyBounds.lean compiles with the same cached Lean
4.32.0/mathlib pin and explicit isolated root. New scalar_fma_bound proves
acc + x*y < 2^62 from canonical limb bounds. Its #print axioms result is
[propext, Quot.sound]; the other three audits are unchanged. Scope 1G/2G,
zero swap, TasksMax=64, lake env lean -j1 -M1600: exit 0, 1.56 s,
peak RSS 1635076 KiB, task swaps 0. Source revision b23f7594 plus this changed
leaf and staged kernel. Evidence: r17-scalar-fma-bounds-r20.log. No full
manifest replay or unchanged generator/regression rerun was needed.

The exact remaining source boundary is still reducer/canonical-operand
correspondence and whole-map equivalence; these range lemmas alone do not
close it. Full privacy, soundness and publication/retry obligations remain.
Next allocation target found in source: WeightAccumulator::fold_dense_arity4
allocates a new vector at every dual fold, although ascending writes to
index i can safely consume the already-read block 4*i..4*i+4 in place.
The post-opening injection also builds temporary scale vectors that the
accumulator immediately copies. Inspect and test those ownership changes
without dropping either verifier or the reference opening check.

## R21 in-place dense dual folds and stack scale scratch

Base 370a08b9 plus this changeset. stage_r17_inplace_fold.py changes only the
isolated staged sumcheck.rs, not the production worktree file. It checks the
exact original SHA256 7e12acf033a9c309a836dcb1c334c69932e15b97407613b3968f8e1c53787ead,
records the replacement hash, and the SBF builder enforces both. No source
pin is waived. fold_dense_arity4 reads the four original values into its
unchanged arithmetic expression, writes the completed output at index i,
and truncates the existing vector after the loop. It no longer allocates a
new Vec at each fold. Injection uses a 22-coordinate stack array instead of
a temporary Vec; the accumulator still owns its validated copy. No verifier,
authentication, opening reference or equality assertion is removed.

Focused optimized tests cover 100 dense-fold schedules over lengths
4,16,64,256,1024, all their rounds and coordinates, against the old allocating
formula. Cases include zero/one/maximal inputs and challenges, and extension
components. All previous map/FFT/basis/serialization controls pass. Actual
host proof accepted and current G-final mutation rejected. Host scope
4G/6G/zero swap: focused exit 0, 28.29 s, peak RSS 535708 KiB;
positive exit 0, 9.36 s, 427048 KiB; negative exit 0, 0.00 s reported,
3344 KiB. All task swaps zero.

InPlaceDenseFold.lean proves unread-block preservation, equality of every
completed output with the original input block's combine value, and bounds
for all four input reads under the source loop's len/4 bound. Combine is
arbitrary: this storage theorem introduces no field identity or hiding
premise. It is a functional storage model, not extracted Rust Vec semantics.
Connecting the actual loop, usize operations and truncation remains a source
refinement obligation; it is not a proof of the entire verifier or privacy.

Smallest-leaf compile: cached Lean 4.32.0, mathlib
81a5d257c8e410db227a6665ed08f64fea08e997, lake env lean with explicit stage
root, -j1 -M1600. Scope 1G/2G/zero swap, TasksMax=64: exit 0, 1.14 s,
RSS 975688 KiB, swaps 0. #print axioms: unread uses propext and Quot.sound;
written and read_in_bounds use propext, Classical.choice, Quot.sound.
No sorryAx or added axiom in the successful audit. Initial focused compile
failed because the minimal import did not introduce the Nat notation ℕ;
using Nat fixed it (failed exit 1, 0.95 s, 954976 KiB, swaps 0). The error
recovery audit in that failed log is not accepted evidence. Source revision
370a08b9 plus this leaf; both attempts are retained. No manifest replay.

R21 SBF source/table/frame checks pass: exit 0, 35.38 s, RSS 618532 KiB,
zero swaps, scope 5G/7G/zero swap. On the same honest fixture at diagnostic
100M, the primary pass reaches injected, tail-folds-end and
primary-terminal-accepted. The last marker reports 69620863 CU remaining:
30379137 CU consumed from the transaction budget to that checkpoint. The
following second semantic-start marker establishes that the primary call
returned and the reference pass began. The latter then exhausts heap;
overall honest execution fails at 30457522 CU. This is **primary-pass
acceptance**, not overall SBF acceptance or a supported-budget result.

The corrupt proof has no primary acceptance marker; its first path exits
during authentication, then the reference path later exhausts heap at
29663590 CU. Overall failure remains a resource error, not an observed
completed negative verifier result. Both 1.2M/1.4M pairs still exhaust CU.
The first dual fold interval is 981291 CU versus R20's 977558; ownership
reuse is a memory improvement, not a CU improvement in that interval.
No G-map, transcript or authentication arithmetic changed. Heap is still
256 KiB, and both passes/reference opening checks remain enabled.

Observation driver exit 0, 0.12 s, RSS 26884 KiB, zero swaps, scope
3G/4G/zero swap. ELF SHA256:
0c29bf29b5215fb1c47e1ff09901ef955844eb52840d2c0683bec0d083e473d9.
Evidence: r17-inplace-fold-host-r21.log, r17-inplace-fold-sbf-r21.log,
r17-inplace-fold-svm-r21.{jsonl,log}, r17-inplace-fold-lean-initial-r21.log,
r17-inplace-fold-lean-r21.log. The current production worktree sumcheck.rs
still matches the original pinned hash above.

The first remaining runtime obstruction is now reference-pass allocation,
not failure to finish the primary relation check. This does not authorize
silently removing the reference or relabeling a primary-only diagnostic as
the full verifier. CU remains far above budget. Source-to-model storage
refinement, whole-transform equivalence and all full privacy/soundness gates
remain open independently of this one-fixture functional result.

## R22 complementary tensor children

Base f51a9bdd plus this changeset. stage_r17_tensor_complement.py computes
right = parent*z once and left = parent-right, rather than computing both
parent*(1-z) and parent*z. A length-1024 vector now uses 1023 full-field
multiplications for splitting instead of 2046, plus subtractions. Descending
parent traversal and output ordering remain; there is no division,
challenge rejection or data-dependent zero skipping. The original source
tensor helper remains retained, and the stage hash chain checks the change.

New optimized gate checks all 1024 Boolean points at all 1024 coordinates
against their scaled one-hot tensors, reusing dirty storage. Existing
extension-field tensor, complete opening-weight, 271 G-basis, FFT, dense-fold
and serialization controls all pass. The actual retained host proof is
accepted and current G-final mutation rejected. Both verifier passes and
opening reference checks remain. Host scope 4G/6G/zero swap: focused exit 0,
28.19 s, peak RSS 535396 KiB; positive exit 0, 9.39 s, 426524 KiB;
negative exit 0, 0.00 s reported, 3344 KiB. All task swaps zero.

TensorComplement.lean proves the split identity and equality of the complete
logical tensor tree for arbitrary list length, ring, scale and coordinates.
It requires no nonzero coordinate premise. This is abstract ring/tree algebra,
not extracted QM31 arithmetic or a source proof of the in-place array loop.
Smallest-leaf compile using the same cached Lean 4.32.0 and mathlib
81a5d257c8e410db227a6665ed08f64fea08e997: exit 0, 0.99 s, RSS 1144260 KiB,
swaps 0; scope 1G/2G/zero swap, TasksMax=64, lake env lean -j1 -M1600,
explicit isolated stage root. #print axioms: split has none; tensor_eq uses
only propext. Source revision f51a9bdd plus this leaf and stage changes.
No unchanged full replay or table regeneration was performed.

SBF source/table/frame gates pass: exit 0, 35.33 s, 618576 KiB, zero swaps,
scope 5G/7G/zero swap. Ordinary first-channel original-weight interval falls
from 3662263 to **2185371 CU**. The G-containing original-weight interval
falls from 17323740 to **16337023 CU**; G tree and FFT themselves are unchanged.
Primary terminal acceptance reports 72084472 CU remaining out of diagnostic
100M: **27915528 CU consumed to the checkpoint**, versus 30379137 before.
The subsequent second semantic-start is reached, then reference-pass heap
failure occurs. Overall honest execution fails at 27993913 CU; corrupt at
27199981. No full-program acceptance or completed checked rejection occurs.
Both 1.2M/1.4M pairs still exhaust CU, and heap stays 256 KiB.

Observation driver exit 0, 0.12 s, RSS 26448 KiB, swaps 0, scope 3G/4G/zero
swap. ELF SHA256:
44746d79e8767f4c61fcdeb959f5ead11d167012ee9e5eaec3b386efdb2d797b.
Evidence: r17-tensor-complement-host-r22.log, r17-tensor-complement-sbf-r22.log,
r17-tensor-complement-svm-r22.{jsonl,log}, r17-tensor-complement-lean-r22.log.
Source field/tree/loop refinement and all full privacy/soundness/retry and
publication obligations remain. These performance and one-fixture functional
results do not discharge any broader security gate.

## R23a hybrid balanced numerator merges

Base dc6ca39e plus this changeset. The R23 staging preflight was corrected
to pass a u8 normalization shift before any compilation; the tested fresh
stage is r23a. Initial Tailscale transfers timed out, then connectivity
recovered. All host jobs used 100.108.41.90, retained caches and zero-swap
systemd scopes. Production paths and prior negative regressions are unchanged.

stage_r17_hybrid_merge.py replaces only the seven fully balanced numerator
nodes of widths 64/128/256 with short convolutions. Small nodes and the
uneven final 256+15 split retain scalar scatter arithmetic. Each child
numerator has degree < n/2, and its opposite denominator degree n/2, so
the product degree is < n: the length-n cyclic convolution has no aliasing.
This is the mathematical design argument, not a compiled source-refinement
theorem. The single existing 2048-CM31 workspace is allocated before the
tree and reused throughout; no additional heap buffer is introduced.

Optimized Rust emits 14 fixed denominator spectra (1536 CM31 constants),
separately from the unchanged original table. The builder pins both tables,
the generator, merge helper, and full kernel modification chain. Generation
exit 0, 26.36 s including compilation, peak RSS 536028 KiB, swaps 0;
scope 4G/6G/zero swap, TasksMax=128. The numerical generation itself is tiny;
compilation dominates. Exact source pins are retained in
evidence/r17-hybrid-merge-source-pins-r23a.json.

Focused optimized controls pass: exact root order/normalization and inverse
round trips at 64/128/256/2048, all 14 spectra inverse-equal their opposite
denominators, and 838 individual merge comparisons including every one of
768 selected-node basis positions, zero, maximum limbs and full-limb vectors.
The existing complete 271-basis G map, ordinary/complete weight, tensor,
folding and arithmetic controls pass. Actual host honest proof accepted;
current-profile G-final mutation rejected (the inherited log label
R17_LEGACY_PROFILE_REJECTED does not describe a legacy fixture).
Focused exit 0, 2.11 s, RSS 284792 KiB; positive exit 0, 9.50 s, RSS
434652 KiB; negative exit 0, 0.00 s reported, RSS 3344 KiB. All swaps 0,
scope 4G/6G/zero swap. Both verifier paths/reference checks are retained.

SBF source/table/frame gates pass: exit 0, 35.62 s, peak RSS 619884 KiB,
swaps 0; scope 5G/7G/zero swap. Observed cgroup peak 951857152 bytes.
ELF SHA256:
6fead68fd11d10d5fd625fd4aab7e5dadee3d59cbbdc8b5654580c344d830099.
The G-tree marker interval falls from 5455352 to 4817466 CU, but the FFT
interval rises from 8525873 to 8923499 CU. Buffer allocation now belongs
to the tree interval rather than the FFT interval; whole-map/checkpoint
comparisons avoid that attribution shift. The second original-weight
interval is 16094716 CU. Primary terminal acceptance costs 27673220 CU
versus R22's 27915528: only 242308 CU saved, about 0.87%.

The full honest execution still fails on reference-pass heap allocation at
27751605 CU; corrupt execution fails at 26957673 CU, not a completed
checked rejection. Both 1.2M/1.4M pairs still exhaust CU; heap is 256 KiB.
Observation driver exit 0, 0.12 s, RSS 26992 KiB, swaps 0, scope
3G/4G/zero swap. Evidence: r17-hybrid-merge-{generate,host,sbf}-r23a.log,
r17-hybrid-merge-svm-r23a.{jsonl,log}. No Lean file changed or theorem was
newly compiled in this experiment. All source-transform equivalence,
full-transcript privacy and soundness gates remain open.

The partial improvement is retained, as is the final-FFT regression. The
next experiment specializes the public transform size/direction and exact
quarter-turn twiddles, with direct comparisons against this generic kernel.

## R24 fixed transform schedules and quarter-turn butterflies

Same base dc6ca39e plus this changeset, fresh stage r24 derived from r23a.
stage_r17_fixed_fft.py instantiates length 64/128/256/2048 and direction as
compile-time constants. The public wrapper selects one of eight kernels.
The exact table has ROOTS[512]=-i and ROOTS[1536]=i. These butterflies use
four base-field additions/subtractions, with no multiplications/negations.
All other twiddles retain the earlier fused butterfly. No mask, mixing
node, transcript byte, challenge, proof format or verifier check changes.
The R23a generic transform is retained as a host-only reference; it is not
compiled into the SBF path. No extra heap buffer is allocated.

Focused release gates pass: 1250 quarter-turn boundary cases and 40 complete
transform comparisons against the previous generic transform (all four
lengths, both directions, zero/max/edge/full-limb vectors), plus every R23a
merge/basis/weight/fold control. The actual retained host proof is accepted
and its G-final mutation rejected, with both verifier paths and reference
opening checks. Focused exit 0, 28.43 s, RSS 536580 KiB; positive exit 0,
9.57 s, RSS 435776 KiB; negative exit 0, 0.00 s reported, RSS 3344 KiB.
All swaps 0, scope 4G/6G/zero swap, TasksMax=128. Compilation dominates
wall time. This is finite source testing, not a universal FFT/source proof.

SBF source/table/frame checks pass: exit 0, 35.57 s, peak RSS 622040 KiB,
swaps 0; scope 5G/7G/zero swap, TasksMax=128. Observed aggregate scope
peak 953937920 bytes. ELF SHA256:
a154b6121d98f0a7a002bb85afb8e9b256a5f873bef27fc0009798b9504ec8d0.
Source pins: evidence/r17-fixed-fft-source-pins-r24.json. Generator and
table are unchanged from R23a, so no unchanged regeneration was run.

| Honest diagnostic interval/checkpoint | R22 CU | R23a CU | R24 CU |
| --- | ---: | ---: | ---: |
| G numerator tree | 5455352 | 4817466 | 3927402 |
| G final FFT section | 8525873 | 8923499 | 6613012 |
| G-containing original weights | 16337023 | 16094716 | 12894165 |
| Primary terminal acceptance, cumulative | 27915528 | 27673220 | 24472669 |

Tree/FFT allocation attribution changes at R23a as noted above. Cumulative
primary saving versus R22 is 3442859 CU, about 12.33%; versus R23a it is
3200551 CU. These two combined changes were measured together in R24;
the reduction cannot be assigned separately to constant specialization or
quarter-turn arithmetic without a further controlled experiment.

Full honest execution still fails on heap in the second reference pass at
24551054 CU; corrupt execution fails at 23757122 CU without a completed
checked rejection. Both 1.2M/1.4M pairs exhaust CU. All cases keep 256 KiB
heap; the 100M budget remains diagnostic only. Driver exit 0 means six
observations captured, not verifier acceptance. Driver wall 0.12 s, peak
RSS 27096 KiB, swaps 0; scope 3G/4G/zero swap, TasksMax=64.

Evidence: r17-fixed-fft-{host,sbf}-r24.log and
r17-fixed-fft-svm-r24.{jsonl,log}. Same retained proof SHA256
a9d851aeeb68193c00791beeae2cbcd0aa894b1ae51e9f051c64020063612fb5
and LiteSVM driver SHA256
34d87c8d4d5cb9b850e22342328ec9cc25e9f36435d982f47c69315ea9dbc2b4.
No Lean file changed or new theorem was compiled; #print axioms is not
applicable to these Rust-only experiments. Existing proved boundaries have
not advanced. First new source-refinement obligation is to identify this
fixed product-tree/FFT implementation with sourceMixedWeight for arbitrary
canonical QM31 inputs, including reduction, no-aliasing, buffer reuse and
actual source loops. It cannot be discharged by the finite controls above.
Reference allocation, supported-budget feasibility, full-transcript privacy,
soundness, shared-oracle, retry and publication gates remain separate and open.

## R25 aligned DIF/DIT storage — rejected CU regression

Base 6a08ffc4 plus this changeset. stage_r17_aligned_fft.py pairs a forward
DIF transform with inverse DIT and separately generated bit-reversed fixed
spectra. Both standalone permutation passes are removed. The new DIF
butterfly forms x=u.a+P-v.a and y=u.b+P-v.b, then reduces
x*w.a+2P²-y*w.b and x*w.b+y*w.a. It cannot reuse the prior DIT butterfly:
the twiddle multiplies a different intermediate. Integer bounds were derived
and compiled before the optimized candidate gate, as requested.

DifButterflyBounds.lean proves padded subtraction safety, the widened product
bound and every raw evaluation-order bound under canonical-limb premises.
In particular, intermediates may exceed 2^63 but are below 2^64. Smallest-leaf
compile exit 0, 1.35 s, peak RSS 1628908 KiB, swaps 0.
#print axioms: padded_difference/raw_bounds use propext, Classical.choice,
Quot.sound; wide_product uses propext and Quot.sound. No sorry or new axiom.
This is not a reducer-residue or Rust-source equivalence theorem.

SpectralReindex.lean proves pointwise product transport and cancellation
through a reindexed convolution pipeline for any coordinate equivalence,
arbitrary forward/inverse functions and a type with multiplication. Compile
exit 0, 0.98 s, RSS 981220 KiB, swaps 0. #print axioms: product uses
Quot.sound; unproduct/convolution_pipeline use propext and Quot.sound.
It does not assume FFT inversion, field or privacy laws. The actual Rust
bit reversal and DIF/DIT transforms still need source correspondence.
Both leaves use the retained Lean 4.32.0/mathlib cached workspace, direct
lake env lean -j1 -M1600 with explicit isolated root/output; each scope is
MemoryHigh=1G, MemoryMax=2G, MemorySwapMax=0, TasksMax=64. Source revision
6a08ffc4 plus these leaves. No full manifest or unchanged replay was run.

Optimized generation permutes 2048 inverse and 1536 merge constants, checking
each merge cell is written once. Exit 0, 26.48 s, RSS 537408 KiB, swaps 0;
4G/6G/zero-swap scope, TasksMax=128. Compilation dominates; no dense arithmetic
or rank search is performed. Builder pins generator, helper, new table,
unchanged old tables and both changed kernel/merge source hashes.

Host controls pass: 15625 new DIF boundary tuples including checked integer
intermediates, all 3584 constants, 20 forward comparisons, 20 independent
inverse comparisons, 20 round trips, all 838 merge controls and the retained
complete G basis/weight/fold gates. Actual honest proof accepted, current
G-final mutation rejected with both verifier paths/reference checks enabled.
Focused exit 0, 2.46 s, RSS 300620 KiB; positive exit 0, 9.64 s, RSS
448712 KiB; negative exit 0, 0.00 s reported, RSS 3168 KiB. All swaps 0,
scope 4G/6G/zero swap. These finite controls are not a universal source proof.

SBF source/table/frame gates pass: exit 0, 35.76 s, RSS 619336 KiB,
swaps 0; scope 5G/7G/zero swap. ELF SHA256:
1a81aae0e40adb2f27d770d268169a9774610e8e936ebf2527e65a1fca855f56.
Primary acceptance costs **28653311 CU**, up from R24's 24472669:
a **4180642 CU regression**, about 17.08%. G tree is 5074950 CU, final FFT
9646106 CU, G-containing original weights 17074807 CU. The combined DIF
arithmetic/schedule change is rejected as a preferred optimization; fewer
permutation passes do not establish lower SBF cost. The precise instruction
cause is not yet isolated, so this is not attributed to one unmeasured cause.

Full honest execution fails in the second reference pass on heap at 28731696
CU; corrupt at 27937764, not a completed checked rejection. Both 1.2M/1.4M
pairs exhaust CU; 256 KiB heap and diagnostic 100M unchanged. Driver exit 0,
0.13 s, RSS 27144 KiB, swaps 0, scope 3G/4G/zero swap. Evidence retained:
r17-aligned-{generate,host-gate,build,lean,lean-reindex,svm-run}-r25.log,
r17-aligned-svm-r25.jsonl, r17-aligned-source-pins-r25.json. Production code,
negative regressions, mixing nodes and transcript remain unchanged.

Next experiment R26 derives from the retained R24, not R25. It keeps the
fast DIT butterflies and absorbs their input permutations into existing
coefficient loads and pointwise spectral products. The permutation lemma
above remains applicable to the algebraic layout, but the paired in-place
source writes need their own correspondence argument and functional gates.

## R26 host-only fused reordering control — not promoted

Fresh r26 derives from R24 and retains its DIT butterflies, scattering
coefficient loads and fusing bit reversal into spectral products. Host gates
pass: all supported indices are in range/involutive, 40 preordered transforms
equal the old FFT, and prior merge/G-basis/actual-proof controls pass. Focused
exit 0, 28.63 s, RSS 535324 KiB; positive exit 0, 9.55 s, RSS 436648 KiB;
negative exit 0, 0.00 s reported, RSS 3344 KiB. Swaps 0, 4G/6G/zero-swap
scope. Evidence: r17-fused-reorder-host-r26.log. No R26 SBF build or CU
measurement was run; this is not a preferred measured implementation.
The user redirected priority to baseline reuse and compact structure before
that measurement, so this pending experiment is preserved, not substituted
for the baseline-reuse work.

## R27 baseline kernel reuse — functional success, heap regression

Fresh r27 derives from measured R24. Source base 6a08ffc4 plus this changeset.
See R17_BASELINE_REUSE.md for the caller/proof reuse audit and the larger
compact-functional boundary. circle_norm.rs, joined_inverse.rs, line_norm.rs,
quotient_fold.rs and affine_primal.rs are byte-equal to the retained baseline;
the stage and builder pin their hashes. The existing line/chord inversion
is shared across both channels, the prepared quotient fold is reused,
v8_affine_primal is enabled, and terminal weights use weight_prefix::<4>
plus the existing four-product helper. No new inverse or field formula.

Batch inverse errors are not returned early: individual inversion is retained
as fallback at the original per-record position, preserving the logical
canonical/domain error ordering. Earlier allocation exhaustion remains a
separate possible behavior and in fact occurs in the SBF diagnostic below.
Both verifier passes and the combined-opening reference remain enabled.

Focused optimized tests pass: 256 two-channel inversion/fold profiles with
zero denominator/base controls and 64 affine-primal/mixed dense-query
terminal cases. The retained honest host proof is accepted and its G-final
mutation rejected. Focused exit 0, 27.72 s, RSS 536248 KiB; positive exit 0,
9.97 s, RSS 442448 KiB; negative exit 0, 0.00 s reported, RSS 3520 KiB.
All swaps 0, scope 4G/6G/zero swap, TasksMax=128. Compilation dominates.
Unchanged FFT/basis suites were not rerun for this opening-only change.

Existing ChordNorm/CircleNorm/JoinedInverse/LineNorm/LineNormBuffer,
QuotientFold, AffinePrimal and TerminalQuery results are reused within their
documented scope. No unchanged Lean file was recompiled; no new universal
caller, source-runtime, full privacy or soundness theorem is claimed.

SBF source/table/frame gates pass: exit 0, 48.93 s, RSS 618744 KiB,
swaps 0; scope 5G/7G/zero swap, TasksMax=128. Added baseline cfg flags
require dependency recompilation; the cached workspace is retained.
ELF SHA256:
d91cb4510ed69e3431f431e17d0d2d752b6265038ad5fadc9f005c466597ff8c.
Preparation costs are unchanged. Query-schedule-end through openings-end is
1736356 CU versus R24's 1986631 CU: 250275 CU saved in that interval.
The new helper allocations exhaust heap during the tail, before primary
acceptance. Thus the 24109158 CU honest failure total is NOT a completed
verifier cost or a better primary checkpoint. Corrupt failure total is
23507686 CU, also a resource failure. All four supported-budget cases still
exhaust CU. Heap 256 KiB and diagnostic budget 100M are unchanged.

Driver exit 0, 0.12 s, RSS 27620 KiB, swaps 0; scope 3G/4G/zero swap,
TasksMax=64. Evidence: r17-baseline-reuse-{host-gate,build,svm-run}-r27.log,
r17-baseline-reuse-svm-r27.jsonl, r17-baseline-reuse-source-pins-r27.json.
R28 retains the reused arithmetic and attempts to remove the regression by
moving/reusing final coefficient buffers rather than allocating each fold.

## R28 owned affine buffers — primary acceptance restored

Base 6a08ffc4 plus this changeset; staged from R27. The existing prepared
affine arithmetic is unchanged. Each final Vec is moved into an owned fold,
old four-entry blocks are read before their lower output slots are written,
and the same Vec is truncated. The retained InPlaceDenseFold storage lemma
supplies the reusable abstract write-order argument; it is not a new proof
of Rust Vec execution or the actual caller. No unchanged Lean replay.

All 240 new owned-fold comparisons pass, covering incomplete chunks, zero
and one challenges and maximal limbs; pointer and capacity are retained.
The 256 shared inversion/fold and 64 affine/terminal controls also pass.
Both host verifier paths accept the retained honest proof and reject its
G-final mutation. Focused exit 0, 27.40 s, RSS 536196 KiB; positive exit 0,
9.98 s, RSS 440540 KiB; negative exit 0, 0.00 s reported, RSS 3520 KiB.
All swaps 0, scope 4G/6G/zero swap, TasksMax=128. Compilation dominates.

SBF source/table/frame gates pass: exit 0, 36.32 s, RSS 621356 KiB,
swaps 0; scope 5G/7G/zero swap, TasksMax=128. ELF SHA256:
39f139dfb4e5c810b63da74d3ccc209271c58d58ed525e49b669ec7e89cc21ec.
The primary terminal now accepts at **24208293 CU**, saving **264376 CU**
against R24's 24472669 (about 1.08%). The opening interval remains 1736356
CU, versus R24's 1986631. Preparation is unchanged at 19892834 CU.

The full honest program still exhausts heap in the unchanged second
reference pass, at 24245690 CU. The corrupt case's full execution fails on
heap at 23507686 CU, not a completed checked rejection. All four 1.2M/1.4M
budget cases still exhaust CU. Diagnostic budget 100M and heap 256 KiB
are unchanged; neither a supported-budget success nor deployability follows.
Driver exit 0, 0.12 s, RSS 27708 KiB, swaps 0; scope 3G/4G/zero swap,
TasksMax=64. Evidence: r17-owned-primal-{host-gate,build,svm-run}-r28.log,
r17-owned-primal-svm-r28.jsonl, r17-owned-primal-source-pins-r28.json.

Next priority is the retained compact ordinary-functional evaluator and its
formal basis/linear-transport composition, as specified in R17_BASELINE_REUSE.md.
Changing expanded-vector transcript binding to a compact descriptor requires
an explicitly versioned research profile and fresh source/oracle obligations.
No production path, G mixing map, verifier check, or negative regression was
removed. Full privacy, soundness preservation and source correspondence remain
open, separately from these arithmetic reuse and resource observations.
