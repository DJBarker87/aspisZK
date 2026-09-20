# R16: distinguish C1 remasking from changing the H1 witness

Date: 2026-09-20. Base privacy revision `76aaddca`.

The phrase "nonlinear C1/H1 coupling" needs a source-specific distinction.
The selected staged host constructs H1 from `compiled.trace`, not from the
separately remasked `trace` used to encode semantic C1. It then adds the
existing H1 padding. This is not permission to choose an unrelated helper:
the registry must read the same constrained tuples that the committed
merged trace represents.

## Complete finite read-set check

`r16_c1_remasking_is_disjoint_from_h1_tuple_inputs` enumerates every producer
and consumer limb in the actual 136-link copy registry. It compares each
referenced cell against the entire relation-free C1 mask inventory, including
the balancing row. Result:

- 2160 cell-read occurrences, 1965 unique row/column coordinates;
- 3803 legal cells in the original inventory;
- intersection zero;
- pivot row 1023 is legal in all 16 columns.

The positive-transfer profile removes one of those 3803 cells, so the checked
superset also covers that profile. The comparison drops the Stable/Late
bank distinction: this is conservative because the merger uses the same
row/column positions with checked disjoint banks. The implementation does
not mistakenly compare copy-output rows instead of tuple-input cells.

`tuple_value` reads only those cell values, constants and public offsets.
`copy_weight` depends on append index and variant, not mask coins.
`pool_v1_pair_forest_copy_rows_v1` compresses them with lambda, and
`build_pool_v1_pair_forest_copy_helper_v1` applies the deterministic helper
builder at chi. Thus, **for a fixed witness/compiler trace, metadata,
lambda and chi**, legal remasking leaves the tuple inputs, compressed rows,
unpadded helper and its pole/success outcome unchanged. H1-pad changes remain
separate. This source read-set argument is not an oracle-independence theorem.

The three inspected source files are unchanged from pinned revision
`9e432896a4e1515efebe940b71fd9b4f9f009189`; `git diff --exit-code` returned 0.
Their SHA-256 values are:

- `pair_forest_trace.rs`:
  `0a97cbba7740acf44e3b85082ff917e6fb60b81a26662a2d7f96acaf0e72309d`
- `pair_forest_hiding.rs`:
  `61bcd59a22c9c02fe3f9ba69cda43bfa8fe02ea14f15da9b761e976fe48798bf`
- `pair_forest_semantic_oracle.rs`:
  `930c9f2211f1bc672195802d6e5de05588a37b48f770d805a5b2d240c8bbf344`

## Execution evidence

`/usr/bin/time -l cargo test --offline --locked --release --jobs 1
-p aspis-prover --lib r16_c1_remasking_is_disjoint_from_h1_tuple_inputs
-- --nocapture`: exit 0; one passed, zero failed. Wall 20.01 seconds;
peak RSS 509394944 bytes; swaps 0. Compilation took 19.56 seconds;
test time rounded to 0.00 seconds. No Lean change or new axioms audit;
no unchanged full regression or host replay. Production source is unchanged.

## What remains nonlinear and unproved

A change of witness changes `compiled.trace`. The retained R7 identity is
still `H1 = D*a(w,lambda,chi) + P*u`, with nonlinear link coefficients and
explicit pole failures. It is not valid to keep this unpadded H1 fixed across
different witnesses. Conversely, there is no additional nonlinear helper
recomputation caused solely by legal C1-mask changes at fixed challenges.

The selected terminal's off-Boolean composition can still change
nonlinearly with those C1 masks. Later-round corrections must handle that
composition, the real witness-dependent incidence offset and the same H1
pad, while preserving the PCS/Final256 posterior. The G-only R14 obstruction
is not removed by this read-set result. Actual shared-seed and shared-oracle
coupling must also justify keeping challenges fixed; source-level read
separation alone does not provide statistical independence.

This narrows the next correction problem without adding a hiding
assumption, refreshing masks, or claiming full privacy/soundness.
