# R17 C1 witness-change correction at actual prefixes

Date: 2026-09-20. Base `017529407b3c1750876fc7dea51445ace646a3a5`
plus this changeset. Fixed-prefix research diagnostic, not full privacy.

## Genuine witness change, restricted observation boundary

The optional `ASPIS_R17_C1_WITNESS_AUDIT` path compiles the opposite private
`selected_second` choice in the retained two-equal-leaves fixture. Both
witnesses validate against the same public statement and settlement
transition. The mode rejects live/complete external contexts and non-honest
fixture cases; this is not an external account or wallet operation.

At the actual old execution's point/OOD/query prefix, it constructs the
compiler C1 difference, then solves a legal mask correction over **M31**
for each of the 16 witness columns. The 108 base-field observation rows are
88 raw values, 12 limbs of three QM31 point claims and eight limbs of two
QM31 OOD claims. The other ten committed C1 mask-only columns are unchanged.
No extension-field mask coins are substituted for base-field coins.

The correction uses the actual relation-free mask inventory, excludes the
dependent row and the reserved positive-transfer inverse cell, and balances
inactive directions. It checks the original matrix times the solution
equals the actual witness-offset target, then checks the resulting delta
with the selected C1 encoder, source multilinear evaluator and source OOD
evaluator. All inactive balances remain zero.

The corrected masked trace is decoded and passed to the actual
`extract_checked` witness/compiler validator. The resulting witness equals
the alternate witness, not merely an assumed valid-witness type. Both
directions pass: old selected=false to true at world0's prefix, and old
selected=true to false at world1's prefix.

Per run: all 16 elimination ranks are 108; 1,408 selected raw values,
48 point claims and 32 OOD claims have zero differences. The balanced
compiler witness difference changes two C1 cells. This is a genuine
witness change in a restricted C1 view, unlike the preceding invisible
H1/G remasking direction.

## Source balancing detail and H1 offset

Source `state_only_hiding.rs` applies masks and then overwrites the last
legal inactive cell with minus the sum of the other inactive cells
(`balance_m31_copy_inactive`, and the loop at lines 699–715). Therefore
subtracting the two raw compiler traces is not in general the difference
between their equally masked, balanced traces.

The diagnostic reconstructs this balancing of the witness difference,
asserting the source inventory's dependent row is 1023 in every column.
The initial v10 implementation compiled, but source inspection identified
this missing step before it was executed. v11 includes it; v10 is retained
as superseded build evidence, not a successful witness-correction result.

The actual helper builder is run on **both compiler traces at the same
lambda and chi**. Both calls succeed in each fixture and the unpadded H1
vectors differ in two rows. This explicitly retains the witness-dependent
helper offset from the R7 incidence argument. C1 remasking disjointness
does not justify setting this offset to zero.

## Not yet preserved

This correction does not preserve C2 roots, H1 observations, semantic
messages, the rest-channel Final256 or relation polynomials. No corrected
complete proof is constructed or published. The unchanged original proof
continues through the normal verifier and rejection controls after the
in-process diagnostic. Its hash is unchanged, which checks audit
transparency, not equality of two full proof distributions.

## Evidence

Stage: `/tmp/aspis-r15-host.drHYn9/r17-two-channel-source-v11`.
Manifest SHA-256:
`a4879bd0e5d40602e4bbc385ff52d8a7e061033daa727cce1f7aabc9d3b9133d`.
Module `tools/r17_c1_witness_audit.rs` SHA-256:
`7550ff993bb6860f62168981fc70d00ae13218303155dd3748cb05589ec99f6a`.
Source pins remain enforced and missing nonhost preimages are not waived.

Offline/locked/release/jobs=1; retained host cache and exact manifest flags.
The focused arithmetic is sixteen small base-field eliminations and source
encoding checks. All listed runs report zero swaps; no Lean change or new
axioms result, and no unchanged full regression replay.

| Target | Exit | Wall seconds | Peak RSS bytes |
| --- | ---: | ---: | ---: |
| v10 host build, superseded before execution | 0 | 48.36 | 736264192 |
| v11 balanced-offset host build | 0 | 48.08 | 638894080 |
| v11 world0 C1 witness change | 0 | 7.93 | 224788480 |
| v11 world1 C1 witness change | 0 | 7.46 | 224919552 |

Logs under the same temporary root: `r17-build-v10.log`,
`r17-build-v11.log`, `r17-v11-world0.log`, `r17-v11-world1.log`.
Original proof hashes remain
`a9d851aeeb68193c00791beeae2cbcd0aa894b1ae51e9f051c64020063612fb5`
and `e81cd45d977e56ce4c5307dc792a468b182dc2d44b2722670aa0a140a38613a7`.

## Next concrete correction

Use the rebuilt H1 offset, not zero, as the affine target. First cancel its
two OOD differences with legal H1 padding. Then use the retained OOD-zero
H1 space to preserve H1 raw/point values while cancelling the combined
C1/H1 rest-channel final difference, with gamma normalization retained.
The required raw/final compatibility must be checked, not assumed from
the earlier zero-target kernel test.

Evaluate the full old/new non-G semantic-coordinate difference in their
respective hidden C1 contexts. Compensate it and the combined first-relation
difference using G while retaining G's entire listed view. This would
advance the fixed-prefix witness coupling; adaptive exceptional events,
commitment/shared-oracle/seed behavior, failures/retries/publication and
soundness still require their separate source-grounded proof obligations.
