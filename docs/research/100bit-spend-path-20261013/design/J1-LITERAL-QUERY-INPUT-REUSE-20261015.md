# Literal opening and query-input reuse inventory

Read-only mapping of existing selected-opening and query-support APIs to the
literal transcript model. The inventory identifies reusable algebraic results
and their still-explicit inputs; it does not derive acceptance or a security
bound for the literal protocol.

## Literal inputs and `MatchingSupport.Data`

`LiteralOpeningView.read` in [`lean/LiteralOpeningView.lean`](../lean/LiteralOpeningView.lean)
reads C1/C2 words, exactly 25 semantic rows, and the ordinary challenges at
25 and 26. Its `View` exposes `word : Fin 29 → InitialWord WideExact`, six
functionals `functionals`, and `baseFunctional`. The word is produced by
`LiteralTypedWords.word ExactBaseProjection.embed eK c1 c2`; the functionals
are produced by `SelectedOpeningFunctionals.functionals` and `rawBase` from
the semantic challenges and two circle points. This is a model construction;
the view does not itself contain the later opening payloads or final word.

The later literal readers are in
[`lean/LiteralOpeningEvents.lean`](../lean/LiteralOpeningEvents.lean):
`readGamma`, `readKappa`, `readFirst`, and `readSecond` read the staged rows
through row 30 and prior challenges. `readSecond` also obtains the literal
folded `VWord` through `LiteralTranscript.vAt`. `LiteralOpeningStages` supplies
the strict row payload decoders and append-stability theorems at the staged
boundaries. The final `.final` opening payload is row 31 in
`OpeningRecordCodec`; it is not part of `readSecond`.

[`lean/SelectedOpeningData.lean`](../lean/SelectedOpeningData.lean) already
provides `SelectedOpeningData.data payloads W V F F0 gamma kappa alpha0 alpha1`.
It constructs `MatchingSupport.Data WideExact` with:

| Data field | Existing source |
|---|---|
| `W` | explicit word argument, available from `LiteralOpeningView.View.word` |
| `V` | explicit `FinalWord` argument; literal counterpart is `LiteralTranscript.vAt` at row 30 |
| `F`, `F0` | explicit arguments; view provides `functionals` and `baseFunctional` |
| `Y` | rows 25, 26, 27 through `SelectedOpeningClaims.Y` |
| `c0` | row 28 |
| `gamma`, `kappa`, `alpha0`, `alpha1` | explicit challenge arguments |
| `p0`, `p1` | row 29 and row 30 via `OpeningPolynomialView.firstPolynomial` / `secondPolynomial` |
| `f` | row 31 `.final` payload |

`SelectedOpeningData.Payloads` groups the seven row payloads (25–31), while
`LiteralOpeningEvents.Second` groups rows 25–30, the V word, and challenges
through `alpha0`. The current interfaces therefore expose most constructor
arguments but do not yet define a single literal reader that combines the
common view, staged second view, row-31 final payload, and four challenges
into `SelectedOpeningData.Payloads` plus a `MatchingSupport.Data`. The exact
typed fields needed are explicit; no equality from a terminal acceptance
check to `MatchingSupport.AcceptedPairing` is included here.

`SelectedOpeningClaims.Y` preserves all six 29-entry values: three point
claim blocks and the extra block from row 25, the before-Z1 block from row 26,
and the gamma payload at row 27. Its `Y_point`, `Y_extra`, `Y_beforeZ1`, and
`Y_gamma` theorems expose those projections. This matters because the extra
row-25 block is not discarded by the selected data constructor.

## Existing list-size and query-support results

The finite set corresponding to query support is
`MatchingSupport.matchingSet d : Finset (Fin 262144)` (not a declaration named
`supportS`). It filters positions by both equations `match0 d i` and
`match1 d i`. `MatchingSupport.Claims d` means that a candidate in
`ConcreteBinding.candidates d.W` satisfies all six functionals and the
constant claim. `MatchingSupport.large_matching_implies_claims` says a support
of size at least 9558 yields those claims, assuming `Good d` and
`AcceptedPairing d`; `no_claims_card_le` gives the contrapositive bound 9557
under those same premises and `¬ Claims d`.

For an actual list-size cap, `ConcreteBinding.candidates_card` gives
`(candidates W).card ≤ 100`. The more general
`JointList.jointInitialList_card_le_100` bounds a width-29 family by 100 when
every tuple agrees with the same lane word on at least 38230 positions.
`PartialJointList.partial_family_card_le_100` reuses that result for selected
coordinates, with zero-padding support of size at least 38230. These are
finite-family bounds, not an executable list decoder or a result that a
transcript-derived family meets the support hypothesis.

`QueryResidualBridge.false_claims_query_containment` is the deterministic
query-support adapter. Given `Good d`, `AcceptedPairing d`, `¬ Claims d`,
`rho ∉ rhoBad iota d q`, every first-fold query equation, and the residual
batch equation, it concludes both `matchingSet d).card ≤ 9557` and every
query `q i` lies in that set. `accumulated_false_claims_containment` derives
the residual equation from a closed sum; `recurrence_false_claims_containment`
adapts the explicit 22-step `QueryAccumulator.run22` equation. No theorem here
connects those premises to literal row-31 verification by itself.

The current conditional sampler adapter is
`UnifiedQueryDensity.query_density_bound`: for a callback fixed by prefix,
message, and table returning `Option (Finset (Fin 262144))`, it bounds the
row-31 event by `choose 9557 22 / choose 262144 22` when the decoded set has
size at most 9557 and the query set has size 22 and is included in it.
`query_first_hit_bound` adds a supplied `FirstReadsBound`. It does not prove
the callback is `MatchingSupport.matchingSet` from the literal transcript or
derive the deterministic support premises above.

## Existing selected opening events and terminal adapters

`SelectedOpeningEvents` defines four bad sets with explicit fixed inputs:

| Event | Payload/context inputs | Cardinal bound |
|---|---|---:|
| `gammaBad` | W, F, row-25/26/27 claims | 336869026622539 |
| `kappaBad` | W, F, F0, claims, row 28, gamma | 600 |
| `firstBad` | W, gamma, weights(F,F0,kappa), row-29 polynomial | 9396508281846 |
| `secondBad` | W, V, gamma, alpha0, weights(F,F0,kappa), row-30 polynomial | 9396508281846 |

`SelectedOpeningEventMass.gamma_mass`, `kappa_mass`, `first_mass`, and
`second_mass` convert these fixed-input cardinal bounds to independent-answer
mean bounds. [`lean/LiteralOpeningDensity.lean`](../lean/LiteralOpeningDensity.lean)
adapts them to literal rows 27–30 using the corresponding staged reader and
prior challenge. If a staged reader returns `none`, that local bad event is
defined false; the density theorem does not establish that an accepted
execution necessarily has a successful read. The opening callback used by
`UnifiedOpeningDensity.opening_density_bound` similarly remains an explicit
prefix/message/table decoder input.

For query-row terminal facts, the old selected interfaces are
`RhoAcceptance.accepted_mem_bad_of_query_miss` and
`SpendQueryDichotomy.dichotomy`: the latter assumes `Good`, `AcceptedPairing`,
sumcheck checks, candidate `OutsideBad`, and no extracted spend witness, then
splits into the rho exception or the small matching support containing all
queries. The rho continuation bound is `QueryRhoAcceptance.continuation_accepted_miss_lt_two_neg_119`, with explicit query continuation, recovered-data/query callbacks, and sampler maps.

The current generic unified terminal adapter is
`UnifiedQueryDecoder.decode_sound` (a successful row-31 parse yields a
31-record context, query ownership/continuation, and output callback), and
`UnifiedRhoDensity.rho_first_hit_bound` gives a conditional row-32 bound for
an explicit recovered `MatchingSupport.Data × Fin 22 → Fin 262144` callback.
These interfaces provide places to plug a concrete decoder; they do not
construct one from the literal opening view.

The older `R0P.MaskD3Glue.accepted_no_hit_extractedZ` consumes a different
abstract protocol: `decisionZ = true`, no hit for `sourceDataWithFallbackZ`,
and an `hfirst` nonzero-gamma condition for every successful old opening
view. It returns an `InputNoteExtracted` trace. Its companion
`SemanticPrefix.large_matching_extracts_of_prefix` instead starts from the
parsed 25-row semantic prefix and still requires explicit typed context and
transport, C2 words, no-hit exclusions, `Good`, `AcceptedPairing`, support
size ≥9558, and sumcheck checks. The current `SpendExtraction.large_matching_extracts`
consumes the latter family of explicit inputs and returns a spend candidate
with production/copy-link/note facts. None of these results currently derives
the terminal acceptance, source-data identity, or callback premises from the
literal readers described above.

## Source pins inspected

| File | SHA-256 |
|---|---|
| `lean/LiteralOpeningView.lean` | `93cfb9df271c07b97050a07e4628f3aa509c03a342d9fa53c05987a368ead557` |
| `lean/LiteralOpeningEvents.lean` | `3be2bd2255d0723eeb03cfce47078d3b36d4ddba5592b0be8f5a1629eb22ece3` |
| `lean/SelectedOpeningData.lean` | `035c7d6b52c7eb80f250414ed68e9711b0dd88e35a04247fa95dab55a2b4a824` |
| `lean/SelectedOpeningStages.lean` | `c87ad5c67f3c57fbc37dc8394a390a8e45c6a6a638c8cae7d0839af4245c1786` |
| `lean/SelectedOpeningClaims.lean` | `e219644ff5ac0049f4a153c8d228bccafc4d4722d23a06bdbf8dfb722710864c` |
| `lean/SelectedOpeningEvents.lean` | `33f96fa95ab309db7ae7f5959b556032c2574d7e7e1449aca40a06d5e48f1949` |
| `lean/SelectedOpeningEventMass.lean` | `5c7ad8017e7dcca60c517d82cad5739cceea3491e7ab5e8b990f401042b46302` |
| `lean/MatchingSupport.lean` | `a3f4eed1b103cdc9cf8b92a3d37a313759e1324a04af79dc251dad8cde775a5b` |
| `lean/QueryResidualBridge.lean` | `392317ece75d5d7b29d034d4425ffb4e95e52b71078e70317339b40fbf1b4aad` |
| `lean/UnifiedQueryDensity.lean` | `b8bc89b66be2347074a22acd69a73ea4e33b81e5092e89c45cac97ef787d47ed` |
| `lean/UnifiedOpeningDensity.lean` | `da14425c9d497daaeffccba3921d0a0283f015a43215b60bbcbd1ebda26d6648` |
| `lean/UnifiedRhoDensity.lean` | `96b14c14f1286e8b5d2164198a4652ef591b827642386966223c89dddf365c8d` |
| `lean/SpendExtraction.lean` | `b1ab643fddcc1ddd4be5e5efa9c7d7291c0067feb9214b2d4bc76a8d8b66a523` |
| `lean/SemanticPrefix.lean` | `a0e75d2bddea2f3d72b7102b29b099e3f552dd50114b255843685c75e8f23245` |
| `lean/SemanticHit.lean` | `320204230140b12cf0494edfeb40d9645ec1fad3813fd0f37ae93578eb12f608` |
| `lean/JointList.lean` | `7649a9557aa960817e357259466573e771b3c2b8ace47dca631d35dc566bf07d` |
| `lean/PartialJointList.lean` | `8ecf2399077ca31a3888bd5cefdc75fdc8cef8fc6dbc310b13f23182d4da68af` |
| `lean/LiteralOpeningDensity.lean` | `32ba2a1e313e8751d65183afea7d218341477a3758b3a6c0b8431d863f4d9250` |
| `lean/UnifiedQueryDecoder.lean` | `b0b1bb84af24193231b6e06f63b84c15e4d527cf76cb968204f1b8a9251c94b4` |
| `lean/LiteralOpeningStages.lean` | `78ef40830007bd0914a7670effd1471bae84abae0494a0179b9f6c72c72ef927` |
| `lean/LiteralTranscript.lean` | `2b76b95f5dffb2856f1af3884859d3d8d16e60bf47c0950559fe3c5e44ec4ed6` |
| `lean/SelectedOpeningPairing.lean` | `bf227c7e561bd3ef66c537f0769565f365d6abff3aaff93aa71c62b3369c1c7c` |
| `lean/ConcreteBinding.lean` | `d7f87db3d7c6d49f6c5c660812b049982fc9314450eeaef202eff7021942876f` |
| `lean/OpeningPolynomialView.lean` | `23ea3b82a3266da3525784a3976769f6bcec33d6d0a5ee07e63fa5675d233730` |
| `lean/SpendQueryDichotomy.lean` | `c8e1c6f175ae584306ba4c7ecb31f7b5646e514e9a08d18e7dc9ed6028cc263b` |
| `lean/RhoAcceptance.lean` | `3a2a9505b457287e2186b272016e09f7ee81035a0489ab9a6b676d891149ad5b` |
| `lean/QueryRhoAcceptance.lean` | `39c9ad1cc388f34728dcabc0f338670a64d8e6b18dffed5a9585a068c9e4fb88` |
| `v8-r0-sem-proof-20261008/lean/R0P/MaskD3Glue.lean` | `7270ca471ad9d35a3db8ab279753df826f2d519bf626115fd4d39d825a303dab` |

Worktree HEAD at inspection: `e4a5808dd061cf373b27d130f7d66eb8f0214db9`.
