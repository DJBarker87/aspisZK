# R16 Final256: required consistency before coverage

Date: 2026-09-20. Base privacy revision `57dc5837`.

The selected source computes the combined encoded polynomial, subtracts the
two-point interpolant, divides by the public OOD chord, and decodes quotient
coefficients q. It checks `q[1023]=0` and the second top-coefficient image
constraint. After the first relation polynomial and challenge alpha, it
publishes `Final256[j] = q[4j] + alpha*q[4j+1] + alpha²*q[4j+2] +
alpha³*q[4j+3]`. Query selection follows this publication.

At each queried fibre, `opened_values_prepared` reconstructs the same four
quotient values from authenticated, gamma-batched raw C1/C2 values and the
OOD interpolant, then applies the normalized circle-to-line fold. These
are not independent of Final256.

## Compiled algebra

`lean/AspisV8R16/FinalConsistency.lean` defines the exact normalized
two-butterfly expression and proves:

- `fold_channels`: folding `A ± yB ± xC ± xyD` gives
  `A + alpha*B + alpha²*C + alpha³*D`, for nonzero x,y,2.
- `zero_raw_forces_zero_final`: if all four raw quotient differences are
  zero, that folded difference is necessarily zero.

This is universal field algebra, not a probability or privacy theorem.
Command: `/usr/bin/time -l lake env lean -j1 -M1800 -R <pack>/lean
<pack>/lean/AspisV8R16/FinalConsistency.lean`, in the cached
`/Users/dominic/ZK/AspisFormal` workspace. Exit 0; wall 8.95 seconds;
peak RSS 1369948160 bytes; swaps 0. Both printed axioms lists contain only
`propext`, `Classical.choice`, `Quot.sound`.

## Exact source-map diagnostic

`r16_final256_source_fold_consistency_all_basis_units` checks all 1024
coefficient basis units on the retained 22-fibre schedule. It compares:

1. The actual encoder's four basis values, fed to the actual
   `qm31_circle_to_line_fold4`.
2. The corresponding 256-coefficient vector with alpha^lane in position
   floor(index/4), fed to `evaluate_final256_coefficients`.

All 22528 comparisons passed for the declared extension-field alpha. This
is exhaustive over coefficient basis units for that schedule/challenge,
not an exhaustive challenge test or formal extraction of the Rust maps.
The test concerns the quotient coefficients, so it does not incorrectly
apply T again to the quotient or to Final256.

Command: `/usr/bin/time -l cargo test --offline --locked --release --jobs 1
-p aspis-prover --lib r16_final256_source_fold_consistency_all_basis_units
-- --nocapture`. Exit 0; one test passed; wall 18.17 seconds;
peak RSS 521240576 bytes; swaps 0. Compilation took 17.66 seconds;
test 0.09 seconds. No unchanged host or full-suite replay was performed.

## Consequence for the remaining correction map

With fixed OOD points, nonzero chord denominators, and unchanged component
OOD values, the interpolant is unchanged. Preserving raw component values
therefore preserves the raw quotient values. Any corresponding change in
Final256 must evaluate to zero at the queried line roots. Thus arbitrary
identity targets across raw openings and all 256 final coefficients are
not the correct surjectivity goal.

For 22 distinct line roots, the expected linear space of final-polynomial
changes vanishing there has dimension 256-22=234, by ordinary polynomial
evaluation rank and the invertible natural-basis conversion. This dimension
calculation is not a certificate that the retained mask posterior covers
that space. Source top-coefficient/image constraints and earlier semantic
observations can further restrict the available corrections.

The next task is the actual compatible-target test: compose the source
quotient/chord/image map with the same retained C1/H1/G coins, preserving
all earlier observations and accounting for the required final/raw
relations. First-three-cut G rank 175 alone does not close that task.
Rounds 3..9, nonlinear H1/C1 dependence, shared-oracle/seed coupling,
publication/failure laws and full soundness remain unproved.
