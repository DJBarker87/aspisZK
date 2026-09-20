# R16 G: first-three-cut and later-view joint diagnostic

Date: 2026-09-20. Base privacy revision `831cb072`.

`r16_g_three_cut_and_later_view_same_coin_diagnostic` checks a single linear
map over QM31 with 1024 columns, one for each original G coordinate. There
is no new G draw or separate coin space for the later observations.

## Observed map

The first 82 rows represent the initial claim and first three semantic
polynomials at a fixed extension-field challenge prefix:

- Round 0 uses all 28 evaluations at 0..27. For degree-at-most-27
  polynomials, these are an invertible coordinate change from the initial
  boundary sum plus the 27 sent coefficients.
- Rounds 1 and 2 each use evaluations at 0,2,..27. The omitted evaluation
  at 1 is fixed by the earlier carried claim and the value at 0.

For each G basis row, the response is the multilinear prefix/current-bit
weight times the actual `state_only_explicit_g_mask_factor` evaluated at
the Boolean suffix of that row. This is the retained R12 row-response
formula. Source `pair_forest_semantic_terminal::terminal_parts` returns G
separately from `original`; the selected mask terminal adds G times that
factor. This isolates the affine G response when all challenges and other
columns are fixed. It does not model re-running Fiat–Shamir after changing G.

The later 93 rows are 88 raw G observations on the retained q22 schedule,
three source multilinear point evaluations, and two OOD evaluations under
the source OOD policy. Raw/OOD coefficient covectors are pulled back through
the same implemented T. Unlike a balanced C1 mask direction, an independent
inactive G unit also contributes to the pivot coefficient: the test retains
that additional term. Original-row point claims are not incorrectly
transformed into encoded-polynomial evaluations.

## Result and certificate

The 175-by-1024 matrix has rank 175. Gaussian elimination constructs a
sparse right inverse using its selected pivot columns. A separate original
matrix multiplication checks all 175-by-175 identity entries. In particular,
the columns of this right inverse for the last 93 targets produce zero in
all 82 earlier coordinates. This is a fixed-prefix correction inside the
earlier affine kernel, rather than a marginal-rank argument.

Command: `/usr/bin/time -l cargo test --offline --locked --release --jobs 1
-p aspis-prover --lib r16_g_three_cut_and_later_view_same_coin_diagnostic
-- --nocapture`. Exit 0; one passed, zero failed; wall 18.84 seconds;
peak RSS 518602752 bytes; swaps 0. Compilation took 17.94 seconds; the test
took 0.43 seconds. The anticipated heavy step was the small fixed-field
elimination and certificate multiplication, executed in the optimized
binary. No unchanged full suite, host replay or Lean compilation ran.

## Boundaries that remain

Challenges and the query schedule are predeclared diagnostic values. This
is not a source transcript or a probability theorem. The first-three-cut
coordinate interpretation is algebraic; the test does not instantiate the
complete selected-terminal fixture or rejected-word/shared-oracle coupling.

In particular, changing G changes C2. Preserving the selected challenge
prefix requires the retained paired-commitment/seed argument to be
instantiated; the test does not assume new independent challenges or hide
that obligation. The eta-after-initial chronology is also not discharged
by a matrix at fixed challenges.

No claim is made for rounds 3..9, Final256, the remaining relation messages,
H1 dependence on C1, seed entropy, visible failures or publication. The
R14 final-round three-high-invariant obstruction for fixed C1 remains in
force. It rules out simply iterating a G-only full-surjectivity argument
through all rounds. This diagnostic neither changes nor reruns that theorem.

The next whole-view algebraic obligation must include Final256's relation
to the raw/OOD observations and the later semantic constraints. Those
observations have mandatory consistency relations, so testing arbitrary
identity targets for the full view would be the wrong condition: actual
witness offsets must lie in the image of one joint correction map. The
soundness and source-oracle obligations remain independent release gates.
