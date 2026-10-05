# Selected R117 mask-only C1 source map

This is a read-only source inventory for the ten mask-only C1 columns (selected C1 indices 16–25). It records mask generation separately from the actual selected research harness's commitment transport. It does not establish a privacy or compatibility theorem.

## Source pins

NUC source root: `/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a`.

| File | SHA-256 | Relevant code |
|---|---|---|
| `crates/aspis-prover/src/state_only_hiding.rs` | `0e8b83d50aaebc65dad86bc63c838d099428a166221990156b9f61164148fe0a` | `build_mask_material_for_layout` around lines 436–477; inactive balancing around 169–181; application around 691–717; `state_only_initial_mask_claim` around 837–874 |
| `crates/aspis-core/src/state_only_hiding.rs` | `18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f` | exponent schedule around 394–395; factor around 601–608; selected evaluator around 647–674 |
| `docs/research/v8-no-work-100-20260907/experiments/performance.rs` | `4c575d4d1004bf39b0bb1f8069495e315e63a7ec9f423a60ec93f3487f4eb8b5` | actual selected R117 commitment harness: lines 195 and 197 |
| `docs/research/v8-no-work-100-20260907/experiments/r16_basis_transport.rs` | `678c64e08e7d14bb6bc160042f0ee01cb39e260748ec1ac95cce008969d586ae` | `transport()` implementation |
| `crates/aspis-prover/src/v6_onefold_prover.rs` | `1715970722d3e183771ff41711a760578deac0522038a3a7d2dd519f90c9a433` | generic selected-column construction around 1218–1230; distinguish from the research harness above |
| `crates/aspis-prover/src/state_only_candidate.rs` | `3bb341ea76057f38b72158d9f882e2a764a5ad85ab0fe5bfcbdb2619a40c6c5d` | generic `encode_state_only_c1_columns` around lines 40–54 |
| `crates/aspis-prover/src/circle_candidate.rs` | `336d10034cb4a37140e5a3645eae7a76cf86a8b6cb2f0c4b8a213e97ac43bd54` | generic `CircleEncoder::encode_c1_message` around lines 482–519 |

## Generation, balancing, and initial claim

The reused generic mask-material builder samples each of the ten `mask_only_c1` arrays as 1024 independent M31 values. It then balances each array over inactive rows by setting the designated first inactive row to the negative sum of the other inactive entries. The ten arrays are returned separately from the sixteen trace C1 columns. The mask application writes relation-free cells only into the sixteen trace columns and balances those columns separately; it does not merge the ten mask-only arrays into the trace.

The selected initial-mask-claim routine evaluates the selected mask expression at all 1024 Boolean row points using the sixteen trace C1 values, the ten mask-only values, and G. Core's mask-only exponents are `[1,3,5,7,9,11,15,17,19,21]`. For lane `j`, the factor is the power of the selected linear mask at exponent `MASK_ONLY_FACTOR_EXPONENTS[j]`, with tower basis `j & 3`. Holding the other inputs fixed, the expression is affine (linear in the lane value) in each mask-only value.

## Actual selected commitment path

The selected R117 `performance.rs` harness forms `selected` at line 195 by chaining `trace.c1` with `masks.mask_only_c1`, preserving the sixteen-then-ten order. At line 197 it applies `r16_basis_transport::transport().forward(m)` to **every one** of those 26 tables before calling `enc.encode_c1_message`. Thus mask-only columns 16–25 undergo the same basis transport as the trace C1 columns before circle encoding. The prior generic-prover summary that described only direct table input was not the selected R117 research harness and should not be used as its source-to-model description.

The transport implementation is pinned above. The generic `v6_onefold_prover` / `encode_state_only_c1_columns` files are listed only to distinguish them from the actual R117 harness callsite; they do not override the selected harness's explicit transport.

## Existing correction evidence and boundary

The archived correction source at `.r21-scratch/r537-privacy-construction-negatives/evidence/c1-source/docs/research/v8-no-work-100-20260907/experiments/r17_c1_witness_audit.rs` uses a zero mask-only array for its selected-mask checks and varies the sixteen trace C1 columns. Its H1/G joint audit labels the tested family `fixed_prefix_only=true` and checks the stated raw, three-point, and two-OOD observations only for that restricted family. The companion `performance.rs` diagnostic appends four actual-source initial-mask equations per trace C1 column and checks the initial claim with the original mask-only and G values held fixed (`R117_C1_INITIAL_MASK_PRESERVED`). `STATUS_SOURCE.md` in that evidence directory describes the same boundary.

Those artifacts do not establish corrections that vary columns 16–25 while preserving raw, three-point, and two-OOD observations. This inventory does not say such corrections are impossible; their joint compatibility remains to be shown. No test, build, or verifier run was performed for this source map.
