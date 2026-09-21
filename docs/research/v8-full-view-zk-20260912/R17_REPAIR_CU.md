# R17 candidate CU measurement

The 1,047,041 CU baseline replay is NOT a repair measurement. The requested
measurement concerns AV8/R17/structuredG271-two-channel/research-v1, including
its changed encoding, structured G and two quotient channels / Final512.
Privacy and soundness preservation remain open regardless of a CU result.

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
