# J5 privacy reuse boundary

Read-only inventory of existing simulator, mask, fold, and rank results. This
note identifies reusable theorem interfaces and their premises; it does not
select privacy parameters or claim a current-protocol privacy result.

## Old checked simulator interface

The R0 reference implementation is in [`R0Z/D12.lean`](../../v8-r0-zk-20261009/lean/R0Z/D12.lean),
[`R0Z/Hvzk.lean`](../../v8-r0-zk-20261009/lean/R0Z/Hvzk.lean), and
[`R0Z/JointView.lean`](../../v8-r0-zk-20261009/lean/R0Z/JointView.lean).
The inspected source hashes are respectively
`272b92f8066f63cf4b57781cfa1f6e586377fadcb1682390acaebda7e4761162`,
`5c8c2abc96eb2e2a7049e2cf0d947856076667dbc7ab00de2758227c0ff904f5`, and
`50d2b0075f4a8a9706d11b49b9da084e07a383fc1144a38cdc0e267530ecd64e`.

`R0Z.D12.MaskImage h B x` is a proposition with two explicit range
obligations. First, for every challenge, witness, and eligible-noise value,
the round-only remainder lies in the range of the common pure-mask map
`(A ... ch).comp inlM`. Second, for any two witnesses with the same public
statement, their base payload-offset difference lies in the range of `A`.
`D12.payload_law` proves an `EqualLaws` translation to the affine map
`t ↦ c + A t` from this premise. `D12.hvzk_perfect_of_maskImage` then proves
`JointView.HVZK_perfect`; it assumes `MaskImage` and does not establish either
range condition. The lower-level checked facts `M_pure`, `decomposition`,
`other_components_affine`, and `g_zero` describe the old payload's affine
split.

The old simulator is defined in `R0Z.JointView.simulator` by applying
`Classical.choose` to `InLanguage h x` to select a witness, then running the
view with uniform mask tapes. `R0Z.Hvzk.hvzk_conditional_of_maskImage`,
`conditional_marginalisation`, `hvzk_perfect_of_maskImage`, and
`hvzk_zero_of_maskImage` compose the conditional affine-law result into exact
interactive-view law equality / distance zero. The chosen witness makes this
a witness-independent law theorem, but not an efficient simulator that takes
only the public statement.

[`R0Z/MaskLayout.lean`](../../v8-r0-zk-20261009/lean/R0Z/MaskLayout.lean)
defines the old legal tape, not an unconstrained full
field vector: `EligibleNoise K F := EligibleCell → F`, `AffTape K F :=
AffCoordinate → F`, and `MaskTape K F := MaskCoordinate → F`, where `F` is a
subfield of `K`. Eligible semantic noise is F-valued and affects semantic
columns below 16 on eligible cells. The affine tape supplies mask-only
columns 16–25, H1 padding 26, G 27, and D 28; extension values are packed from
four F coordinates. Balancing and H1's copy-active restriction are part of
the model. The source comments explicitly exclude salts from these tape
coordinates. This declaration is not the current R1 full-mask distribution.

## Semantic trace and chain-mask results

`R0Z.Chain.sRem_mem_chain0` in
[`Chain.lean`](../../v8-r0-zk-20261009/lean/R0Z/Chain.lean) proves that the old
normalized witness-difference remainder lies in `Chain0`, assuming an honest
prover/build, basis, statement, witness, challenge, noise, and
`alpha ch 9 ≠ 1/2`. `Chain0` records zero non-round coordinates, the initial
sum relation, nine transitions, and terminal evaluation zero. This is a
membership result; it does not prove that `Chain0` is in the image of the
silent mask map.

The checked `R0Z.PureRounds.silent_mem_chain0` is not present in this
worktree's current tree. Its immutable source is available at
[`PureRounds.lean` on commit `700dd4b4a0aeb45ab51a416e8e145aace2d096a9`](https://github.com/DJBarker87/aspisZK/blob/700dd4b4a0aeb45ab51a416e8e145aace2d096a9/docs/research/v8-r0-zk-20261009/lean/R0Z/PureRounds.lean#L42-L70).
It assumes the pure mask image has zero `nonRound` projection and concludes
that this image is in old `Chain0`. Its companion `mem_silentMasks_iff`
expands this to zero mask-sum, point/extra claims, OOD, inactive sum,
opening/final coefficients, and opened values. Neither theorem supplies the
R1 payload correspondence or the remaining chain-image inclusion.

[`R0Z/Z4Maps.lean`](../../v8-r0-zk-20261009/lean/R0Z/Z4Maps.lean) defines
`roundMask_surjectivity` and `c1_surjectivity` as propositions, not proofs.
The former asks for a silent-mask preimage of the
specific normalized round remainder; the latter asks that a particular
public-instance C1 projection difference lie in `range c1Map`. The files
state that no rank computation or unrestricted onto-ness is installed.

## Folded and repeated disclosures

The current R1 algebraic helper
[`DualPadWord.lean`](../lean/DualPadWord.lean) proves `repair_mem`,
`repair_raw_zero`, and `full_word_eq` for a common K-linear word subspace and
an explicit per-lane noise preimage with matching raw observations. It does
not produce those preimages. [`DualPadLift.lean`](../lean/DualPadLift.lean)
specializes cancellation to `gamma^27` and `gamma^28` in a rootless
quadratic extension, with `gamma.im ≠ 0`, and proves whole-word equality plus
preservation under any fixed deterministic observation. It proves no rank
or view-law premise.

[`SecondFoldMatched.lean`](../lean/SecondFoldMatched.lean) has
`SecondFoldMatched.second_match`: if `alpha` is outside the exact `B6`
bad-set for four repeated small words, a support `S` has at least 2390
positions, and the response curve agrees on `S`, then four component
messages match on `S` and the small message has the stated weighted
decomposition. This is an encoder-level matching result with those explicit
assumptions; it is not a simulator or a law for the published folded view.

[`RepeatedLift.lean`](../lean/RepeatedLift.lean) defines the complete
four-lane fibre support and proves `repeated_support_card = 4 * S.card`.
`repeated_projection_agrees_on_support` assumes fibre constancy and that the
projected encoding equals the four-value mean. `repeated_lift_projection_descent`
also assumes `64 ≤ S.card` and a distinct-message agreement bound of at most
255, and concludes equality with the projection. Its comment explicitly
leaves encoder/projection identities and overlap bounds as hypotheses.
[`FractionalLiftInvolution.lean`](../lean/FractionalLiftInvolution.lean)
proves a polynomial fractional lift is an involution up to a scalar, with
degree and field-cardinality premises. These are useful algebraic/fold
interfaces; none gives a complete privacy law for the current disclosed
folds and openings.

## Query and random-oracle exposure

`R0Z.HonestView.PayloadCell` in
[`HonestView.lean`](../../v8-r0-zk-20261009/lean/R0Z/HonestView.lean)
includes semantic coefficient arrays,
point claims, extra claims, OOD values, mask sum, opening/final coefficients,
and opened values indexed by query, child, and column. Its `Challenges`
record contains 25 semantic scalars, two circle points, four opening
scalars, and a query set. `R0Z.FsStatement.ROMView` adds the observer's own
query/answer transcript and explicitly omits the prover's private
oracle-input log.

[`FsStatement.lean`](../../v8-r0-zk-20261009/lean/R0Z/FsStatement.lean)
defines `ZK_FS` as a target. `ROMReduction` is an explicit
open proposition requiring a common randomized extension and real/ideal
comparison bounds. `R0Z.FsGood.zkfs_of_hvzk_on` composes a supplied
good-challenge HVZK theorem, a supplied ROM reduction, and a supplied bad-mass
bound. `GoodDensity.badAlpha_density` in
[`GoodDensity.lean`](../../v8-r0-zk-20261009/lean/R0Z/GoodDensity.lean)
proves the old uniform `K^10` alpha
exception bound `21 / |K|`; it does not give the corresponding law for the
current WideExact sampler/history or cover the extra `gamma ∈ K` exception.

Current R1 normalized transcript views and row-specific sampler laws preserve
the abstract row payload/challenge; no checked theorem maps every current
published value (semantic masks, C1/C2 leaf data and salts, fold outputs,
circle/opening values, queried openings, and terminal output) into the old
`Payload` and legal mask-tape experiment. In particular, the old mask tape
has no salt coordinates. Thus D12's query-inclusive old view is not yet a
simulator for the current R1 query exposure or its shared-oracle execution.

## Rank facts: formal targets versus finite probes

The inspected Lean sources contain no universal rank/determinant certificate
for the current raw observation map. `roundMask_surjectivity` and
`c1_surjectivity` remain proposition definitions; the current
`DualPadWord`/`DualPadLift` results consume explicit preimages and do not
derive them. `SelectedCircleWeights.circleWeight_base4` is a checked symbolic
weight-factor identity, not a rank theorem.

The retained runtime rank gate at
[`proof-rank-gate-p3`](../evidence/privacy-wide/proof-rank-gate-p3/README.md)
records one accepted P3 transfer proof: 16 eligible C1 maps have rank 112
each; the balanced H1 map has rank 94 in ambient dimension 95; the
compensated pure-round image has rank 1080 and its initial-zero part has rank
1076. The measurement is tied to the logged proof, transcript challenges,
and 22 query positions. It is finite runtime elimination, not a checked
certificate for all inputs/challenges or a theorem that H1 is onto. The
`wide-full-g0/g1` runs and proof-rank-gate v1–v3 likewise report finite
experiments. The numerical rank outputs should not be promoted to universal
matrix facts.

The current raw-map dimensions and the distinction between the C1, H1, and
pure-round measurements are recorded in
[`PRIVACY-RAW-MAP-INVENTORY-20261015.md`](../PRIVACY-RAW-MAP-INVENTORY-20261015.md)
and [`PRIVACY-RANK-REUSE.md`](../PRIVACY-RANK-REUSE.md). Those inventories
also give the source pins for the probe and old Lean map definitions.

