# R4 sampler and prefix transport

Branch `codex/cx-r4-transport-20261021`, base `9b9b652a9`.
Status: work in progress. No boundary premise is removed.

## Stage 1: frozen-path inventory

The source pins and sizes are in `evidence/r4-transport-20261021/source-inventory.json`.
The selected path is S2 (two folds); S1 places queries/rho at 30/31 and is outside this claim.
The latest C3 addendum identifies `R1FinalSoundnessHeadline` as the consolidated endpoint,
which retains `h_R4_transport : s.R4_transport`. R19 is its earlier predecessor.

| Rows | Shipped call | Selected Lean model | Existing evidence / open join |
|---|---|---|---|
| 25,26 | r1_wire circle_validated; sampler circle_sample; secure_ood_circle_point_from_parameter with fixed fallback | SelectedChallengeMap circle views; R0P circleSample0/1 | Extracted wrapper policy and QM31 totality exist; exact point equality, current caller and full prefix still required |
| 27 | Transcript scalar(nonzero=true); sampler gamma_sample | OpeningSamplerBound gammaSample / ModuloField nonzeroRank | Optimized low-base-P quotient folding is not the legacy binary reducer; pinned PreparedModel leaves B.gamma free |
| 28,29,30 | Transcript scalar(nonzero=false); sampler ordinary_sample | OpeningSamplerBound sample / ModuloField fieldRank | Pinned PreparedModel leaves B.ordinary free; serialize inactive and round payloads, including root || round1 |
| 31 | Transcript queries; core queries_from_pairs; QueryScan scan / finish | QuerySamplerBridge, Q22WordScan, SamplerWords | Mask low 18 bits, stable first22, at most64 draws; iterator and selected-state joins remain |
| 32 | Transcript scalar_k; sampler qm31_sample | rhoOf (sigma32 block) = SemSource qm31Sample | Existing extracted sampler arithmetic can be composed with successful block call |

Field input words are **not rejected** when >= P: all 256 bits form one little-endian rank.
QM31 and ordinary reduce modulo P^4 and P^8; gamma reduces modulo P^8-1 then adds1.
Circle mapping uses one parameter and fixed row fallback, not parameter retries.
Row31 rejects duplicate masked candidates, consumes at most eight blocks, and rejects if fewer
than22 distinct indices occur. The stop guard is before each word: filling slot22 on word8
consumes the next block before stopping, except at the eighth block. The returned state is
that selected advance, not unconditionally advance7. All eight pairs are hashed eagerly by
the shipped wrapper even when the selected advance is earlier.

`r0_sample_row` is explicitly provisional and rejects row32; it is **not** the deployed
33-row caller. Legacy Transcript challenge_qm31 rejection sampling is also not this path.
D86 concerns the builder S2 transport, not a proof of all challenge samplers. D88/PHASE2
constructs a protocol model and explicitly retains Rust sampler/parser/execution joins.

## Stage 2: focused sampler work

Pending.

## Stage 3: prefix composition and remaining boundary

Pending.

## Validation

No compiler or verifier attempts in stage1. Source inspection only.
