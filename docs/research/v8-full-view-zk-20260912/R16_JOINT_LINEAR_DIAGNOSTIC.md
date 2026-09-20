# R16 same-coin raw/point/OOD diagnostic

Date: 2026-09-20. Base privacy revision `1d77761f`.

The focused test `r16_joint_raw_point_ood_same_coin_diagnostic` builds ONE
matrix per witness column, with the SAME source-derived mask directions in
every observation block. It does not introduce fresh masks between blocks.
There are 108 M31-valued rows:

- 88 raw values on the retained revealing q22 schedule;
- 12 limbs of the three original-row multilinear point claims;
- 8 limbs of two transformed-polynomial OOD evaluations.

The points are fixed deterministic diagnostic values, not sampled by a
source transcript. `v6_statement_points` supplies the actual three-point
map. The multilinear weights are checked against `WeightAccumulator` at
all 1024 rows for each point. The two OOD points satisfy the actual
`secure_ood_circle_point_from_parameter` policy. Their coefficient factors
use the staged host's natural circle basis formula. The actual encoder
supplies the raw basis values.

For every available legal mask direction, the test constructs its original
unit vector (balanced at 1023 when inactive), applies the implemented T,
and checks that it is the claimed single coefficient direction. It excludes
the balancing coordinate and positive-transfer cell (column 3, row 1014).
It then certifies all 108 identity targets and verifies the correction
matrix by multiplication, using the existing exact affine certifier.

## Result

All 16 witness columns have rank 108 in this fixed joint test. Available
direction counts for columns 0..15 are:

`[221,221,222,222,223,223,223,223,223,247,248,258,258,258,258,258]`.

An explicit negative control restricts each matrix to the first 89 pad
directions used by the raw-only argument. The certifier returns a verified
separator for the full 108-dimensional identity target in every column.
This prevents treating those 89 directions as unlimited fresh joint pads.
It is a failure of full surjectivity, not on its own a witness separator.
The original C1 negative regression is unchanged.

## Exact execution evidence

Each run used `/usr/bin/time -l cargo test --offline --locked --release
--jobs 1 -p aspis-prover --lib
r16_joint_raw_point_ood_same_coin_diagnostic -- --nocapture`.
Time was expected in compilation; the fixed small eliminations used the
optimized binary. No host/Lean/full-manifest rerun was needed.

| Changed test stage | Exit | Wall seconds | Peak RSS bytes | Swaps | Test seconds |
| --- | ---: | ---: | ---: | ---: | ---: |
| Initial columns 0 and 10 | 0 | 18.25 | 513359872 | 0 | 0.08 |
| All 16, source-weight and transport cross-checks | 0 | 18.52 | 514277376 | 0 | 0.20 |
| Final, added 89-direction negative control | 0 | 17.71 | 515883008 | 0 | 0.27 |

All three commands ran one test, with zero failed; final compilation took
16.98 seconds. These are executable certificates, not new Lean theorems;
an axioms audit is not applicable to this change.

## What this does NOT establish

It does not establish universal joint coverage at arbitrary/adaptive
challenges, the actual seeded mask distribution, a public-only simulator,
or coverage after conditioning on semantic messages. H1/C2 correlations,
the other committed columns, all semantic coefficients, Final256, remaining
relation messages, oracle queries, visible failures and publication are
absent. Their omission is not permission to ignore them in the full proof.

The next privacy obligation is a correction in the same coin space that
also preserves the earlier semantic/helper observations, or an exact
separator showing why that fails. A new full-rank test for this smaller
subview would not close it. Soundness obligations are tracked separately
in `R16_SOUNDNESS_OBLIGATIONS.md`.
