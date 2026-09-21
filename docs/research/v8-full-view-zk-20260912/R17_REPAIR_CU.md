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
