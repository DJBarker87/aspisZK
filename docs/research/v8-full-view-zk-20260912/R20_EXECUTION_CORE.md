# R20 execution-core: measured improvement, target OPEN

2026-09-22. Best complete clean primary: **2,865,333 / 2,866,803 CU**.
Both genuine R19 proofs accept at the 100M diagnostic cap. Both exhaust the
actual 1M cap, at unchanged 262,144-byte heap. **The packet's under-1M objective
is not complete.** Resource failure is not counted as checked rejection.

Implementation commit: `da2bc4808481f9450e8a048cfff3ada1cf3e28f0`, branch
`research/v8-r20-execution-core-20260922`. Research stagers only; repository
production crates unchanged. No push, merge, deployment, wallet operation,
new privacy profile, hiding assumption, or security closure.

## Pins and reproduction

Base `c9315d8b05efb2cdad976bb0f4db3574f1c24577`; all seven Git blob pins
and 29 packet payload hashes match. Archive SHA-256:
`0e0b25bb5df2a98c58a32124329084c508df364b1f8fddbd05b05737c3d99c14`.
The unmodified packet is under [r20-pack](r20-pack/CODEX_TASK.md).

The actual accepted assembled R19 canonical-a workspace supplied 164 verified
file pins and baseline ELF
`7a8aebda609d17257e454a3d2ca968906eaed704267148c9063fcdc9e906b0ee`.
The stager validates every input pin and records before/after hashes.
Legacy R18 `source_revision` is not the R20 base; use
`r20_execution.base_git_commit` and `r20_execution.source_changes`.

Selected clean stage:
`/home/dombarker/project-offloads/aspis-r20-clean-20260922-b`.
ELF SHA-256:
`fbaaab12e5f0e798dde28626abadb61cff69354cabb2dcf3f1125559efb2db8c`.
Source manifest SHA-256:
`5ca2f89be94ed727be1e1352b411204682fbe46fc64e91893021688d562456c0`.
The 699-field wire, oracle/transcript chronology, sparse G slots, T163, both
roots and all image terms remain. Reference removal is not counted again.

Reconstruct using `tools/stage_r20_execution.py` from canonical-a into a fresh
directory with:

```text
--opening --digest --shared-prepare --shared-geometry
--semantic-basis --sparse-whole --private-dot --clean
```

Do not select `--factored`, `--fine-profile` or `--dot-micro` for this variant.
The micro option deliberately builds an arithmetic experiment, not a verifier.

## Implemented and source-checked boundary

- Prepared beta/gamma coefficients retain the mixed-width C1 kernel and
  complete canonical decoder, including zero coefficients at beta=0/1.
  The mixed interpolant is hoisted. Authentication uses the original bytes.
- Ordinary preparation and terminal chord geometry are shared, retaining
  pivot, inactive-row, image and final relation contributions.
- Whole-dot arithmetic has checked canonical entry, four-product u64 bounds,
  a 4096-term cap and unchanged general full-u64 reducer. SBF measurements
  select the private packet-dot backend, not a replacement public field API.
- Ten actual semantic challenge bases are retained in a verifier-owned
  271-field heap cache (4336 bytes including constant coin). Host execution
  asserts old Horner and all 271 old source coin values. No prover cache hint,
  transcript reordering or mask resampling is introduced.
- Sparse G processes one group at a time; whole dots replace normal and high
  contractions. All 128 intermediate sums, zero extension, carry boundaries
  and eight final halvings remain. This is not the optional scalar transpose.
- Digest factoring preserves actual fixed/optional events, 20 append levels,
  carry case, empty roots and right-side tweak; both packed output lanes are
  independently compared on arbitrary opened values. Expected-digest sums
  still use scalar arithmetic. No large by-value copy saving is claimed.

These have executable source differentials and algebraic/range reasoning,
not a machine-checked universal Rust equivalence theorem. **No Lean file was
changed or compiled**, and no new axioms audit or privacy theorem is claimed.

## Complete execution measurements

Totals are SVM `meta.compute_units_consumed`, not program-log consumption
(56 CU smaller). Non-clean candidates below are instrumented.

| Variant | World 0 CU | World 1 CU |
|---|---:|---:|
| Pushed R19 | 3,279,621 | 3,280,813 |
| R19 clean baseline | 3,277,163 | 3,278,356 |
| Prepared opening only | 3,095,605 | 3,096,655 |
| A: opening, digest, shared preparation/geometry | 2,991,711 | 2,992,829 |
| C: A + semantic basis and core whole-dot sparse | 2,888,693 | 2,889,754 |
| E: C + private canonical dot | 2,873,106 | 2,874,576 |
| Optional factored T163 | 2,910,498 | not rerun after regression |
| **Selected clean B** | **2,865,333** | **2,866,803** |

Clean-to-clean savings: 411,830 / 411,553 CU (about 12.6%). Corrupted-final
diagnostic runs reject with Custom(6) at 1,736,700 / 1,732,289 CU. All four
corresponding 1M runs exhaust resources. Clean B removes 61 checkpoint calls;
raw logs confirm no checkpoint program logs remain.

The optional T163 factoring passes 48 actual ordinary/dense/reference checks
(including shared geometry) and 48 arbitrary image/final checks, but costs
37,392 CU more than E on world 0. It is retained as a rejected experiment.

Work moved between stages is counted: A's semantic-rounds + G/final cost is
142,903 + 439,229 = 582,132 CU. C's pair is 297,570 + 181,451 = 479,021 CU.
Basis reuse increases the earlier cost but lowers the pair by 103,111 CU;
the complete-primary saving is 103,018 CU.

## Checks actually executed

| Check | Result |
|---|---|
| Unmodified packet C++ with sanitizer | pass; integer bounds and nine synthetic budget controls pass |
| Packet Rust release build | compiles; **zero tests** in standalone package |
| Actual source opening differential | 32 authenticated arbitrary sets; six betas; 3344 canonical positions; 88 poles; root/record/query/frontier/error-order controls pass |
| Actual semantic digest helper | 1440 arbitrary cases, two public variants, 36 index patterns; literal and retained tensor outputs agree |
| Actual whole-dot/private backend | 512 vectors through length 4096, maximal limbs and malformed/bound controls pass |
| Semantic basis | 2560 rounds, scaled coins and stale/reordered-cache negatives pass |
| Actual sparse G | 295 cases, all 271 bases, all four outputs and 128 sums equal |
| Private canonical arithmetic | 200,000 vectors, halves 0..30, malformed limbs and full-u64 reducer edges pass |
| Final clean host | both frozen genuine proofs pass; independent full host reference retained |
| Final malformed/canonical/authentication suite | **3281 cases pass**, including one honest control and 2796 noncanonical fixed-field limbs; zero old-profile fixtures supplied |
| Cached SBF compilation | selected clean B exit 0; all 1024 source basis entries verified; no frame-overflow diagnostic |
| Actual budget gate | **exit 1 / FAIL**, correctly rejecting exhaustion and incomplete runs |

Actual assembled arithmetic micros compare scalar, prepared-3, four-dot and
whole-dot kernels. At n=27 the first micro measured 17,358 / 9704 / 11,012 /
7333 kernel CU respectively. A later same-ELF core/private comparison measured
7192/6833 (n=27) and 40,576/38,893 (n=163). These are not verifier totals.

## Resources and retained evidence

NUC via Tailscale, cached release toolchains, offline/locked dependencies and
two compilation jobs. Heavy scopes use MemoryHigh=5G, MemoryMax=7G,
MemorySwapMax=0, TasksMax=128. Smaller SVM/packet/malformed scopes use 2G/3G,
swap0. Recorded jobs report zero swaps; ambient old host swap is distinct.
Unrelated V7 work and wallet keys were untouched. No large Lean replay ran.

Raw logs retain commands, wall time, peak RSS, exit and swaps; manifests retain
compiler flags and source hashes. See `evidence/r20-*`, particularly
[clean receipt](evidence/r20-clean-b/budget-receipt.json),
[failing gate](evidence/r20-clean-b/budget-gate-result.json),
[recomputed E intervals](evidence/r20-combined-e/audited-diagnostic.json), and
[source gates](evidence/r20-source-gates-a/r20-source-gates-a.json).

Preserved plumbing failures: missing workspace member, missing vec import,
oversized seed literal, nonexistent conversion API, ambiguous integer type,
and wrong include path. Each retry corrected its cause. Clean A was stopped
after an invocation omitted `--clean`; clean B is the corrected fresh stage.
These failures are not protocol-rejection evidence.

## First remaining execution obligation

Deliver a source-equivalent complete run below 1M, not just a cheaper dot.
E's world-0 diagnostic intervals still include semantic 880,280 CU (including
retained basis), preparation 249,648, ordinary terminal 785,531, records
337,234, authentication 139,513 and G/final 170,590. Semantic plus preparation
alone is 1,129,928 CU. A free G terminal cannot close the gap.

Still unexecuted: whole-dot expected-digest accumulation, detailed preparation
and record subkernel attribution beyond current checkpoints, finer ordinary
tensor/correction attribution, optional scalar-transpose A/B, and additional
independently generated source fixtures. No optimistic operation-count
multiplier substitutes for those measurements. The packet remains OPEN.

Universal joint-view privacy, adaptive posterior retention, real shared-oracle
challenge law, coherent pre-beta quotient extraction, and retry/publication
accounting remain separate R19 obligations. R20 closes none of them. The C1
negative regression and earlier privacy boundaries are preserved.
