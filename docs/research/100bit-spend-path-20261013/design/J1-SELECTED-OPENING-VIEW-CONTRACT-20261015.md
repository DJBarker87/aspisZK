# J1 selected-opening view contract

This note records the current Lean model interface for the selected opening
binding rows. It is a representation contract only. It does not connect the
payloads to Rust execution, recover them from accepted input, or prove an
accepted-prefix or causal-recovery statement.

## Selected six-vector view

`AspisR1.SelectedOpeningClaims.Y` maps typed payloads to six vectors in this
fixed order, each with 29 `WideExact` entries:

| `Y` index | Payload source | Lean accessor |
|---:|---|---|
| 0–2 | row 25 circle payload | `CircleRecordCodec.pointClaims row25 point` |
| 3 | row 25 circle payload | `CircleRecordCodec.extra row25` |
| 4 | row 26 circle payload | `CircleRecordCodec.beforeZ1 row26` |
| 5 | row 27 gamma payload | `row27` |

Each element is the `.val` of a `LowWide` value. `Y_im_zero` records that all
six vectors lie in the low subfield. The companion `parts` function places
`c0` at index zero and places the 29-term gamma-weighted sum of `Y j` at
index `j+1`. `parts_weighted_sum` states that weighting those seven entries
by powers of kappa is exactly `JointFunctionalBinding.claimedValue Y c0 gamma
kappa`.

`SelectedOpeningClaims.lean` has a green focused compile: attempt g, source
SHA-256 `e219644ff5ac0049f4a153c8d228bccafc4d4722d23a06bdbf8dfb722710864c`,
2.21 seconds, 3,586,452 KiB peak RSS, zero swap, and six standard-only axiom
reports. The six-vector projections, low-subfield fact, and weighted-sum
identity are therefore checked for supplied typed payloads.

## Opening polynomial view

`OpeningPolynomialView.polynomial` at
`docs/research/100bit-spend-path-20261013/lean/OpeningPolynomialView.lean:22`
uses ascending monomial order. For each of
the two typed seven-coefficient opening payloads, the view proves degree at
most 6 and identifies the boundary expression as coefficient 0 plus
coefficient 4. This is the polynomial representation consumed by the
two-round comparison model; it does not prove that a Rust Horner evaluation
uses this representation. Attempt b is green at source SHA-256
`23ea3b82a3266da3525784a3976769f6bcec33d6d0a5ee07e63fa5675d233730`, 2.31
seconds, 3,569,460 KiB peak RSS, zero swap, and seven standard-only axiom
reports.

`SelectedOpeningData.lean` packages the selected payloads as
`MatchingSupport.Data E`, keeping `W`, `V`, `F`, `F0`, and challenges as
explicit inputs. Its projections preserve `Y`, `c0`, and `f`, and it reuses
the two degree≤6 results. Attempt a is green at source SHA-256
`035c7d6b52c7eb80f250414ed68e9711b0dd88e35a04247fa95dab55a2b4a824`, 2.20
seconds, 3,573,720 KiB peak RSS, zero swap, and five standard-only axiom
reports. This remains model construction from supplied data, not recovery of
that data from a proof transcript.

## Relation to the older opening view

The old `R0P.MaskView.openingViewZ` at
`docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean:180` consumes
25 semantic rounds followed by
`beforeZ0` and `beforeZ1` circle rounds. Its statement builds the opening
claim from the three `beforeZ0` vectors, while the `beforeZ1` vector is matched
as `_` and discarded. It also requires the 25-challenge parse, C2 base
condition, distinct circle points, and both non-rationality conditions before
returning an opening statement. The old `openingViewZ_of_parsed` theorem is at
`MaskView.lean:195`; the current
`SemanticPayloadOpeningView.opening_view_of_payloads` wrapper is at
`docs/research/100bit-spend-path-20261013/lean/SemanticPayloadOpeningView.lean:25`
and passes those same conditions explicitly.

Consequently, that old view remains useful for the three claims and its
existing opening statement, but it does not itself expose the current six
vectors: in particular it does not retain row-25 `extra`, row-26 `beforeZ1`,
or row-27 gamma payload as entries of `Y`. The new selected view makes those
payload positions explicit without asserting an equation between them and an
accepted proof.

## Source pins

The hashes below pin the source text cited above against source base
`2778b34d38aa1f24be04ef07bdf665bdab36aeef`. The three selected-module files
are working-tree additions on that base; their green focused attempts are
recorded in `evidence/lean-selected-opening-data-20261015/` and the polynomial
and six-vector results in their own evidence bundles.

| Source | Relevant declarations | SHA-256 |
|---|---|---|
| `lean/SelectedOpeningClaims.lean` | `Y`, `parts`, projection/subfield and weighted-sum lemmas | `e219644ff5ac0049f4a153c8d228bccafc4d4722d23a06bdbf8dfb722710864c` |
| `lean/SelectedOpeningData.lean` | `Payloads`, `data`, projection and degree lemmas | `035c7d6b52c7eb80f250414ed68e9711b0dd88e35a04247fa95dab55a2b4a824` |
| `lean/OpeningPolynomialView.lean` | `polynomial`, degree and boundary lemmas | `23ea3b82a3266da3525784a3976769f6bcec33d6d0a5ee07e63fa5675d233730` |
| `lean/SemanticPayloadOpeningView.lean` | `opening_view_of_payloads` | `bb3a10730f44cd10abeb0e581a818365963512841a4e4d7b4be6542760d57454` |
| `lean/JointFunctionalBinding.lean` | `claimedValue` and comparison definitions | `9a63100ea4e301a813c001beee84e5b4938748d8c429901f1668f6b54f344a19` |
| `lean/CircleRecordCodec.lean` | typed row-25/26 payload accessors | `b1fba8dced40f86c1b7d1f28eef2c6c25df720f36ffd9a18b464d6a57296f71f` |
| `lean/OpeningRecordCodec.lean` | typed row-27 gamma payload | `7ac150cff7ede99cf4916e81e8ba348bdcf785e6d7771cf46aa9622756fd6387` |
| `v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean` | `openingViewZ`, `openingViewZ_of_parsed` | `f27198834fa43256002cce83de7eeef675fecd88e89db0ee7a2bc00ef3a8b44b` |
