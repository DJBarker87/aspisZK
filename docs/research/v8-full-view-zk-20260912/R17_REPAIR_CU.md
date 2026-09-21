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
