# Pure semantic-round reuse inventory

Read-only inventory of the historical `R0Z.PureRounds` module and its direct
imports `R0Z.Shift`, `R0Z.Chain`, and `R0Z.Z4Maps`. The inspected source is
commit `700dd4b4a0aeb45ab51a416e8e145aace2d096a9` (parent
`5ff677bf36be5af137b29f9bf09c819bfb29073c`). No branch was imported or
cherry-picked, and no build or replay was run. This note reports declaration
shapes and dependency scope only.

## Generic round identities

The useful theorem groups are in `docs/research/v8-r0-zk-20261009/lean/R0Z/`.

`Shift.rounds_eval_of_vdeg` (`Shift.lean:269-295`) states that, when
`f : (Fin 10 → K) → K` has `VDeg 10 (fun _ => 27) f`, evaluation of
`PayloadSplit.rounds ch j f` at `z` equals the sum of `f` over Boolean tails
at `roundPoint ch j z`. `eval_rounds_nine` (`:297-302`) gives the last-round
evaluation at `alpha ch`; `evalRound9_roundInclusion_rounds` (`:304-309`)
reconstructs that value from the old payload's round-coefficient arrays.
These are polynomial interpolation facts. Their present APIs still use
`Challenges` and `PayloadSplit.rounds`.

`Chain.rounds_initial` and `rounds_chain` (`Chain.lean:86-106`) give the
initial Boolean-sum identity and the adjacent-round boundary recurrence for
any degree-bounded `f`. `roundPoly_rounds` (`:171-175`) reconstructs a round
polynomial from the monomial coefficients of `PayloadSplit.rounds`.

`PureRounds.selector_round_match`, `selector_round_mismatch`,
`linear_round_match`, and `tail_sum_selector` (`PureRounds.lean:133-213`)
provide the selector, weighted-coordinate, and Boolean-tail identities used
by the closed forms. `power_rounds` (`:263-296`) is the general closed-form
polynomial statement: it handles
`a ↦ τ * (q + (∑ i, weights i * a i)^e) * ∑ r, selAt a r * u r`, for
`e ≤ 26`, and expresses round `j` as a sum over rows with prefix factor
`eqPrefix (alpha ch) r j`, current-bit factor
`if rowBits r j then X else 1-X`, and the corresponding affine power in
`X` and `β weights (alpha ch) j r`.

Special cases are `pureRound_maskOnly` (`:298-310`), `pureRound_G`
(`:312-319`), and `pureRound_libra` (`:419-427`). They instantiate the same
row formula for the mask-only power, the degree-26 G power, and one of the
56 Libra monomials. `pureLibra_maskSum` (`:429-436`) is the matching Boolean
sum identity. Supporting degree lemmas include `weighted_vdeg`,
`word_vdeg`, and `power_word_vdeg` (`:222-243`), plus
`coordinate_power_vdeg` and `coordinate_power_round` (`:376-417`).

These generic identities are the reuse candidates for a new round-function
API. Their proofs and statements depend on the old `Challenges` parameter
through `alpha ch` and on the old `PayloadSplit.rounds` interpolation wrapper;
they do not take an R1 seven-row payload, an R1 challenge record, or a gamma
parameter. `roundPoint` (`HonestView.lean:168-172`) reads `alpha ch` only.

## Results tied to the old PCS payload

`PureRounds.A_pure` (`PureRounds.lean:17-21`) identifies the old
`(A π B ch).comp inlM m` map with `PayloadSplit.L π B ch (pureTrace B m)`.
`roundPoly_L` (`:23-29`) and `L_maskSum` (`:33-38`) expose the old payload's
semantic round polynomial and mask-sum coordinates. `silent_mem_chain0`
(`:42-70`) proves a zero-nonround old payload image lies in the old `Chain0`.
`mem_silentMasks_iff` (`:72-102`) expands the old `silentMasks` predicate
into zero conditions for `.maskSum`, `.pointClaim`, `.extraClaim`, `.ood`,
`.inactiveSum`, `.openingCoeff`, `.finalCoeff`, and `.opened`; the
`.semanticCoeff` family is precisely the round-data family omitted from
`nonRound`.

`L_pure_maskOnly`, `L_pure_G`, and `L_pure_libra` (`PureRounds.lean:688-740`)
are closed forms after embedding a restricted old mask tape `m : M K F` into
`PayloadSplit.L` and reading it through `Chain.roundPoly`. Their coefficient
corollaries (`:758-802`) select old `.semanticCoeff j i` cells. The Libra
mask-sum corollary (`:742-756`) selects old `.maskSum`. These statements
require a concrete R1-to-old-payload correspondence before their payload
implications can be reused; the statements themselves do not provide one.

`Z4Maps` (`Z4Maps.lean:14ff`) defines old payload projections/maps including
`roundProjection`, `roundMaskMap`, `silentMasks`, `silentRoundMaskMap`, and
`c1Projection`/`c1Map`. Its `roundMask_surjectivity` and `c1_surjectivity`
are proposition definitions, not proofs of the surjectivity properties.

## Challenge and payload layouts

`R0Z.HonestView.Challenges K` (`HonestView.lean:30-36`) has fields
`sem : Fin 25 → K`, `circle : Fin 2 → Point K`,
`opening : Fin 4 → K`, and `queries : Finset (Fin 262144)`. The derived
coordinates are `alpha ch i = ch.sem (15+i.val)` and
`zc ch i = ch.sem (3+i.val)` (`:38-39`). Although there is no field named
`gamma`, `batchLinear` (`:191-194`) uses `ch.opening 0 : K` as the lane
batching challenge, with coefficient `(ch.opening 0)^c.val`.
The separate R1 `MatchingSupport.Data.gamma` field has type `E`
(`lean/MatchingSupport.lean:35-39`); this inventory finds no declaration
identifying it with an R0Z challenge field.

The old `PayloadCell` (`HonestView.lean:53-65`) distinguishes semantic
round cells `.semanticCoeff (round : Fin 10) (coefficient : Fin 28)` from
`.openingCoeff (coefficient : Fin 7)` and
`.finalCoeff (coefficient : Fin 256)`. In `linearPayload`
(`HonestView.lean:208-220`), `openingCoeff i` is coefficient `i` of the
`relationLinear (openingWeights π ch)` applied to `batchLinear π ch`; the
`finalCoeff i` cell is projection `i` after `foldLinear (ch.opening 3)` is
applied to that batch. The honest payload values (`:323-336`) spell these as
`(roundPolynomial (batchLinear π ch t) (openingWeights π ch)).coeff i.val`
and `foldMessage (ch.opening 3) (batchLinear π ch t) i`. The widths 7 and 256
belong to those old PCS payload cell families; they are not the seven raw
D18 coefficient rows or the 28 coefficients of each semantic round.

## Source hashes

SHA-256 values below are over the file contents returned by `git show
700dd4b4:<path>`.

| Module | Repository path at pinned commit | SHA-256 |
|---|---|---|
| `R0Z.PureRounds` | `docs/research/v8-r0-zk-20261009/lean/R0Z/PureRounds.lean` | `227c7f5886841b6678da2189cb0196f5d3f286b44887512a35468d54c4b704c4` |
| `R0Z.Shift` | `docs/research/v8-r0-zk-20261009/lean/R0Z/Shift.lean` | `253d7afbcc38f1295d5bd3231916762595bc2174cbd77ec57b7f153b91ed3b4a` |
| `R0Z.Chain` | `docs/research/v8-r0-zk-20261009/lean/R0Z/Chain.lean` | `c0e5ce0ffd53bee97a8ac9a7c66be4b6d639aac296259416f7799ccaa3e0a4e8` |
| `R0Z.Z4Maps` | `docs/research/v8-r0-zk-20261009/lean/R0Z/Z4Maps.lean` | `5e92064e8f9f0f71a5da98a139f1dba8fa3b4463e40831e317f22246e0c63ceb` |
| `R0Z.HonestView` | `docs/research/v8-r0-zk-20261009/lean/R0Z/HonestView.lean` | `f331f2b7e0ffc7c755328d9c1b7d318990fcfca14d2bb63ba3f185611a8c7446` |
| `R0Z.PayloadSplit` | `docs/research/v8-r0-zk-20261009/lean/R0Z/PayloadSplit.lean` | `fca4444e9f8ebd1949a48d9bf71636beb5b80626459dbabcfc05173327a8e285` |
| `R0Z.Partition` | `docs/research/v8-r0-zk-20261009/lean/R0Z/Partition.lean` | `138e2bdce877cfc8d962e11cb1e0110eeb23c0c9623182d927c38dc07ad95c0f` |

No R1 portability, privacy, or security gate is asserted by this inventory.
