# V8 audit: convergence of the Lean tree on the two goals

Base `4e0f47381` (`research/v8-r64-guarded-m31-20260929`), 2026-10-05.
Profile `AV8/R102/sparseG-bitperm-two-swaps/quadratic-channel-fold/merkle8-research-v1`.
Inputs: `manifest.json` (80 nodes), `leaf-map.csv` (2,128 rows), `import-graph.json`,
skeleton under `lean/V8Audit/`.

"Closed" means: the node statement is exactly an existing theorem, bound in the
skeleton by name and typechecked with only `propext`, `Classical.choice`,
`Quot.sound`. Nothing else is called proved.

## 1. Node counts

| Pillar | closed | conditional | open | deferred | total |
|---|---:|---:|---:|---:|---:|
| Privacy | 25 | 6 | 21 | 0 | 52 |
| Soundness | 6 | 4 | 16 | 0 | 26 |
| Refinement | 0 | 0 | 0 | 2 | 2 |
| **Total** | **31** | **10** | **37** | **2** | **80** |

| Kind | closed | conditional | open | deferred |
|---|---:|---:|---:|---:|
| algebraic | 15 | 3 | 6 | 0 |
| probabilistic | 9 | 5 | 13 | 0 |
| oracle | 5 | 2 | 5 | 0 |
| composition | 2 | 0 | 13 | 0 |
| refinement | 0 | 0 | 0 | 2 |

Neither goal is closed. `PrivacyGoal` cannot hold as stated: all seven ledger
terms are UNASSIGNED at this base, so `epsilon_total` is undefined
(`PRIVACY_LEDGER.md`: "No numerical global privacy bound is assigned").
`SoundnessGoal` has explicit numeric targets summing to `2^-104.26`, but two of
the nine round targets rest on an extraction premise that is not proved
(`B_SOUNDNESS_100.md`).

All 31 closed nodes are lemmas about fixed mathematical objects: algebraic
identities, determinant-zero fractions under product-uniform laws, and laws of
oracle programs on independent answers. No closed node mentions the R102
prover, verifier, transcript or view; the tree has no Lean model of them. Every
node that does is open, conditional or deferred.

## 2. How much of the Lean tree feeds a closed or conditional node

A file feeds a node when it lies in the transitive import closure of the file
holding that node's bound theorem. A conditional node inherits the closure of
the closed theorem that gives its reduction.

| | files | lines |
|---|---:|---:|
| Tree under `v8-full-view-zk-20260912/lean/` | 2,128 | 275,441 |
| Feeding a closed or conditional node | 1,344 (63.2%) | 177,245 (64.3%) |
| of which reachable from a privacy node | 1,336 | 176,392 |
| of which reachable from a soundness node | 31 | 3,055 |
| ORPHAN | 784 (36.8%) | 98,196 (35.7%) |

The feeding share is concentrated. One node, P28 (the complete-223 determinant
grid bound, R885), has 1,021 files and 151,636 lines in its closure: 48% of all
files and 55% of all lines exist to certify one probability bound of
`14049/m` under a fixed-root product-uniform law. The next largest closures are
P27 (R941, 382 files), P25 (R727, 333), P26 (R714, 285), P30 (two-swap fixed
root, 265), P31 (R588, 229).

Orphans by reason:

| Reason | files | lines |
|---|---:|---:|
| refinement-deferred | 348 | 37,166 |
| generated-chunk-of:&lt;file&gt; | 199 | 44,366 |
| unused | 127 | 10,011 |
| superseded-design | 110 | 6,653 |

Classification rules, applied mechanically in this order: (1) transitively
imports Aeneas, or lives in an `AspisR<n>…` extraction directory, or is
imported only by such files: refinement-deferred; (2) name ends in a chunk
index (`Chunk07`, `Row03`, `Blocks12`, …): generated chunk of its first
non-chunk importer; (3) directory `AspisV8R10`–`R15`, `AspisV8H1C2`,
`AspisV8R17`, or an R19 file of the T163-ordered certificate chain
(`FixedQuery*`, `HighWitness*`, …): superseded-design; (4) otherwise unused.
"Unused" means not consumed by any node of this skeleton; several unused files
are earlier or alternative forms of bound results (see clusters 9, 12 below).

## 3. Ten largest orphan clusters

Clusters are weakly connected components of the orphan import subgraph
(93 components in all).

| # | files | lines | Content | Reason |
|---:|---:|---:|---|---|
| 1 | 274 | 30,886 | Aeneas-extracted execution chain: `AspisR136`–`AspisR618` directories and the R19 files that replay sampler, transcript, serializer, gamma-batch and combine-beta execution against them (49 sinks) | refinement-deferred (269), unused (5) |
| 2 | 107 | 22,264 | R17 source-minor block certificates: `SourceLowerBlocks`, `SourceBlockSupport`, `SourceWindowBlocks`, `SourceDiagonalBlocks`, `SourceBlockEntries` and their `SourceMinor*` aggregators. The R17 active minor was rebound for the two-swap order in R698–R714 | generated-chunk (97), superseded-design (10) |
| 3 | 82 | 21,443 | R769/R772/R780 point-0/point-2 weight and dual-leaf chunks with no aggregator in the tree (56 sinks) | generated-chunk (82) |
| 4 | 60 | 4,724 | Private coefficient, norm, batch-prefix and reverse-loop execution (R221–R358) | refinement-deferred |
| 5 | 32 | 1,341 | T163 fixed-query polynomial and high-witness chain (R43–R50); replaced by `TwoSwap*` (R121) | superseded-design (17), generated-chunk (13), unused (2) |
| 6 | 21 | 1,287 | Source-shaped limb, refill, scan and permutation laws (R444–R466) | unused |
| 7 | 15 | 633 | R13 shared-oracle and R14 prefix-disclosure models of the pre-R16 profile | superseded-design |
| 8 | 13 | 1,477 | Paired-commitment aggregate, salt counting, V8 leaf instantiation, R9 operational bridge | unused (11), superseded-design (2) |
| 9 | 12 | 574 | First-round generic privacy lemmas (`AffineMask`, `BalancedMasks`, `DCompensation`, `GatedRelease`, `RetrySymmetry`, …) | unused |
| 10 | 10 | 875 | OOD parameter/distinct retry laws and R17 rejection-cursor models | unused (6), superseded-design (4) |

Next in size: causal first-hit and duplex-collision bounds (10 files, 682
lines, unused); the R826–R856 joint-repair chain superseded as statements by
R887–R941 (9 files, 565 lines, unused); the semantic degree fragments
R374–R386 (9 files, 1,048 lines, unused; they would support soundness node
S10).

## 4. Critical path

The minimal set of open nodes whose closure proves each goal modulo the
deferred refinement node. Composition nodes are listed because they are open
in Lean; each is mechanical once its inputs exist.

**Privacy** (modulo P02). Prerequisite that is not a node: assign a number to
each of the seven ledger terms.

1. P03 seed hop (oracle)
2. P04 salt hop (oracle)
3. P09 merkle8 paired-commitment trace and bad mass (oracle), then P05c
4. P10 honest challenge segment first-read (oracle), then P06c
5. P11 joint sampler chronology law (probabilistic)
6. P12 witness-independence of pole and abort events (probabilistic), then P07c
7. P13 transfer of the four determinant bounds to the adaptive law (probabilistic)
8. P14 universal C1 108-row coverage with initial claim (algebraic)
9. P15 fold-free ordinary residual (algebraic) — Question A
10. P16 exact chord image (algebraic) — Question A
11. P17 inactive balance (algebraic; conditional on a source fact inside P02) — Question A
12. P18c, giving P18
13. P19a G-step premises (algebraic), then P19c, giving P19
14. P1A view-preserving coupling (composition)
15. P1B retry and publication law (probabilistic)
16. P08c, giving P08; then P01

14 leaf claims and 7 composition steps.

**Soundness** (modulo S02).

1. S24 list caps at the exact parameters (algebraic; V7 theorems exist, not rebound)
2. S20 pre-gamma tuple list covering every accepting branch (probabilistic) — Question B
3. S11 OOD pair (probabilistic)
4. S12c, giving S12
5. S21 pre-beta quotient pair (probabilistic) — Question B; then S13c, S14, S17
6. S22 far-final accepted mass (probabilistic) — Question B
7. S15c, giving S15 and S16
8. S18 relation rounds (probabilistic)
9. S23 payment-witness extraction (probabilistic)
10. S10 semantic rounds (probabilistic)
11. S03 Fiat–Shamir compilation for the R102 transcript (oracle)
12. S04 arithmetic; S01

10 leaf claims and 4 composition steps.

## 5. Skeleton compile record

Pinned Lean 4.32.0, build host, `lake env lean -j1 -M4500`, one systemd scope
per file with `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`,
`TasksMax=128`. The shared cache `aspis-r126-release-20260930-a/lib` was read
through symlinks; outputs went to a separate audit directory. Source revision
`4e0f47381`. No manifest or package replay was run.

| Target | SHA-256 (first 12) | exit | wall | peak RSS KiB | swap | axioms |
|---|---|---:|---:|---:|---:|---|
| `lean/V8Audit/PrivacyAlgebra.lean` | `52062ae54e00` | 0 | 1.66 s | 4,107,424 | 0 | 14 reports, standard three only |
| `lean/V8Audit/PrivacyOracle.lean` | `9732ae0292a6` | 0 | 1.26 s | 3,265,916 | 0 | 11 reports, standard three only |
| `lean/V8Audit/Privacy.lean` | `951ddc9fb0cf` | 0 | 1.48 s | 3,350,848 | 0 | no theorem in file |
| `lean/V8Audit/Soundness.lean` | `f153a8b27584` | 0 | 1.01 s | 2,071,436 | 0 | 6 reports; `node_S32` uses `propext`, `Quot.sound` only |

Fifteen existing leaf modules that the bound theorems need were absent from the
shared cache and were compiled once each, unchanged, into the audit output
directory: `AspisV8Privacy/{FiniteGames, PrivacyGames, HybridBudget,
AdaptiveComposition, RetryFailureBound, SeparatorObstruction}`,
`AspisV8R18/SparseCoordinates`, `AspisV8R19/ChannelFold`,
`AspisV8R17/{RawFinalCoverage, TwoChannelImageGate}`,
`AspisV8H1C2/FiniteTransport`, `AspisV8PairedCommitment/{Table, ShadowTable,
GoodEvent, Marginals, ForwardHop}`. All exit 0; wall 0.43–1.12 s each; peak RSS
at most 2,300,604 KiB; zero swaps. Five first attempts failed on import
resolution (a package root present in two search-path entries) before the cache
was mirrored by symlink; no memory cap was raised and no source was changed.
The skeleton itself needed three corrections before the recorded runs: universe
arguments for `type_of%`, a missing `.ir` link, and the qualified name
`AspisV8R15.ExactTowerBase.QM31Exact`.

Mismatches recorded under rule (d): none of the 31 attempted bindings failed.
S24 was not attempted: the V7 list-cap and correlated-agreement theorems live
in `AspisFormal/AspisFormal/K1/`, outside the audit search path, and are stated
for V7 objects; S24 is therefore open, not closed.
