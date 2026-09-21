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

Remaining: compile and execute the specialized candidate, address real SBF
heap/stack/CU limits without dropping checks, then measure the integrated
complete transaction. No repaired CU number is available yet. No deployment,
external transaction or wallet operation occurred.
