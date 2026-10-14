# Privacy payload reuse inventory (read-only)

Source snapshot: current task worktree `HEAD=e21211727fc6ad53a2ef014d3fa3dda72037cef0`; old PureRounds source is read from `codex/t2b2a-purerounds-20261013` at commit `700dd4b4a0aeb45ab51a416e8e145aace2d096a9`. This is a mechanical declaration inventory, not a privacy conclusion.

## Existing R0 zero-initial/terminal chain facts

- `R0Z.Chain.rounds_initial` (`docs/research/v8-r0-zk-20261009/lean/R0Z/Chain.lean:87-96`) takes `ch : Challenges K`, `f : PayloadSplit.PointFunction K`, and `hf : VDeg 10 (fun _ => 27) f`; it states the sum of round-0 polynomial evaluations at 0 and 1 equals Boolean sum of `f`. `rounds_chain` (`:98-106`) with the same `ch/f/hf` and `j : Fin 9` relates the next round's two evaluations to the previous round at `alpha`.
- `R0Z.Chain.Chain0` is defined at `:144-145` as `InitialChain0 ch` intersected with the kernel of final round-9 evaluation at `alpha ch 9`. `mem_chain0_iff` (`:156-164`) spells out: non-round coordinates zero; initial round sum zero; all nine transitions; terminal evaluation zero.
- `R0Z.Chain.sRem_mem_chain0` (`:275-289`) takes honest prover `h`, basis `B`, statement `x`, witness `w`, challenge `ch`, noise `n`, and only `hgood : alpha ch 9 ≠ 1/2`; it proves the witness-difference remainder `sRem h B x w ch n ∈ Chain0 ch`. Its construction uses `g_mem_initialChain0` plus `Phi0_sRem`. It is a property of the R0 model's semantic-round arrays, not a statement about the full R1 transcript.
- `R0Z.PureRounds.silent_mem_chain0` (`codex/t2b2a-purerounds-20261013:docs/research/v8-r0-zk-20261009/lean/R0Z/PureRounds.lean:42-70`) takes `h,B,ch,m` and `hs : nonRound ((A h.transport B ch).comp inlM m) = 0`; it proves this pure mask image lies in `Chain0 ch`. The condition is precisely a zero-nonround condition; it is not a premise about arbitrary legal R1 payloads.
- `R0Z.PureRounds.mem_silentMasks_iff` (`:73-103`) expands silent-mask membership into zero maskSum, all point/extra claims, OOD, inactive sum, opening/final coefficients, and opened values for the pure image.

## R0 normalization and distribution interfaces

- `R0Z.MaskLayout` (`MaskLayout.lean:44-61, 72-120`) defines `EligibleNoise := EligibleCell → F`, `AffTape := AffCoordinate → F`, and `MaskTape := MaskCoordinate → F`; `F` is a subfield of `K`, with `[Algebra (ZMod P) K]`. Its comments state salts are not coordinates of this tape (`:8-10`). Semantic eligible noise affects only lanes `<16`; affine tape fills mask-only lanes 16–25, H1 padding lane 26, G lane 27, and D/libra lane 28 (`:100-120`). These are the R0 legal mask parameter spaces.
- `R0Z.D12.M_pure` (`D12.lean:41-51`) says `payload h B x w ch (m,n) = payload ... (0,n) + A ... ∘ inlM m`; it requires explicit `h,B,x,w,ch,m,n` and uses `A` as the common pure linear map.
- `R0Z.D12.decomposition` (`:53-77`) says each `payload ... t = c ... + A ... t + roundInclusion (g ... t.2)` for `t : T K F`; this is the field-level source/model decomposition.
- `R0Z.D12.payload_law` (`:107-114`) proves an `EqualLaws` translation to the affine map `t ↦ c + A t`, but requires `hm : MaskImage h B x` and public-witness equality. `MaskImage` (`:101-105`) itself requires both round remainders and between-witness base offsets to be in specified linear images. `hvzk_perfect_of_maskImage` (`:120-140`) is conditional on that `MaskImage`; the file explicitly says it is not installed/proved by this interface.
- `R0Z.PayloadSplit.run_split` (PayloadSplit.lean around `:176-190`) is the cellwise translation of the R0 `run` model into linear-mask part `L` plus original part `O`, under its concrete `applyAff`/`applyEligible` construction. `R0Z.Chain.roundPoly_originalRounds` (`Chain.lean:177-181`) then maps the round coefficient arrays to the old sumcheck `rounds` polynomial. These are R0-internal translations; no declaration here takes the R1 `Message M` type.

## R1 current normalized-view and payload interfaces

- `R1.TranscriptView` (`lean/TranscriptView.lean:11-40`) has `Message M = initial State | payload M`; its `Challenge Cv` wraps an ordinary `Cv` or query `Except Nat (List Nat)`, paired with a duplex `State`. It has no R0 `PayloadCell`, affine tape, or eligible-noise argument.
- `UnifiedSampler` (`lean/UnifiedSampler.lean:21-70`) quantifies over arbitrary `{M Cv}`. It takes `Message M` as prover input; `samp` chooses initial/plain/reseed/query samplers based on row and constructor. `messageValid` is only a proposition describing the constructor schedule (`:41-44`). `UnifiedRun.message` (`lean/UnifiedRun.lean:17-19`) maps row 0 to `.initial c1` and later indices to `.payload (payload i)` for arbitrary `payload : Nat → M`.
- `UnifiedInitialLaw.sampler_law` (`lean/UnifiedInitialLaw.lean:19-34`) translates the initial row's own sampler to an independent mean over the duplex challenge/state for fixed `pub,a,c1`; it does not randomize or translate `c1` or a payload mask. `decoded_bound` preserves that fixed-row bound as a premise (`:36-49`).
- `UnifiedPayloadStep.payload_step` and `payload_reads` (`lean/UnifiedPayloadStep.lean:19-44`) establish only the deterministic absorb/advance state transition and the ordinary-row read addresses for an arbitrary abstract payload. `reseed_step/read` (`:46-63`) add the tag-based reseed address. They do not express an R0 field payload or a distribution on legal masks.
- `UnifiedSemanticActualView.actual_output` (`lean/UnifiedSemanticActualView.lean:18-79`) is a typed representation equality for `1 ≤ n < 26`, requiring `hD`, `hl : p.lbl 0 = 160`, and `he : p.enc (payload 0) = PublicInitFrame.emptyRecord`. It equates the decoder's ordinary prefix/message/challenge view to `UnifiedRun` for semantic row `n`; it does not map that `M` to `R0Z.HonestView.Payload`.
- `UnifiedOpeningView.actual_output` (`lean/UnifiedOpeningView.lean:20-79`) gives the analogous representation equality for rows 27–30 (with `k<4`) and same `hl/he`. `UnifiedQueryView.actual_output` (`lean/UnifiedQueryView.lean:19-84`) gives row 31 representation equality, also assuming table values agree with `H`. `UnifiedSemanticFacts.semantic_records_have_cells_and_squeeze_reads` (`lean/UnifiedSemanticFacts.lean:19-109`) gives decoded-record cells and squeeze-read facts with explicit trace consistency, read bound, and no-collision premises; it is not a mask payload law.
- `SemanticOpening.Witness` (`lean/SemanticOpening.lean:20-51`) is an `E`-valued 29-lane candidate plus three point-claim equations, one extra-claim equation, and codeword typing. `claims_imply_witness` (`:53-80`) gets this from `MatchingSupport.Claims` and `CandidateDescent.WordTyped`. It uses `coeffWeight_eq_tensorPoint` to align the D18 point formulas. Circle rows are separate explicit inputs to `rows`; this witness is not a translation from the full arbitrary message `M` to R0's mask tape.
- Initial candidate-list facts (`lean/InitialResponses.lean:25-67`) prove a 100-element Lambda list and existing full-width list theorem consequences. They express a deterministic finite list, not a distribution over masks.

## Literal coverage comparison

R0's `PayloadCell` (`R0Z/HonestView.lean:53-65`) comprises 10×28 semantic coefficients, 3×29 point claims, 29 extra claims, 2×29 OOD values, inactiveSum, 7 opening coefficients, 256 final coefficients, and 262144×4×29 opened values. The R0 `Challenges` record (`:30-39`) groups 25 semantic scalars, two circle points, four opening scalars, and a query set. Its mask tape fields are separate from salts and from public metadata.

R1's shared view exposes an abstract prover message at every payload row plus the challenge/state (`TranscriptView.lean:11-40`); current view theorems preserve that value rather than normalize its contents. The R1 semantic witness covers its candidate tuple, three point claim rows, extra row, and codeword typing; the circle rows remain supplied separately. No searched theorem translates all R1 published values—C1/C2 leaf material and salts, both fold outputs, semantic/point/extra values, circle/opening values, terminal coefficients, opened query values, and final query/rho output—into one R0 `Payload`/legal-tape vector. The old R0 declaration also has no explicit C1/C2 leaf salts as tape coordinates. Current R1 frame/parsing and transcript-equality lemmas are per-encoding/per-row interfaces, not a common R0 payload law.

## Source hashes

- R0Z Chain `c0e5ce0ffd53bee97a8ac9a7c66be4b6d639aac296259416f7799ccaa3e0a4e8`
- R0Z D12 `272b92f8066f63cf4b57781cfa1f6e586377fadcb1682390acaebda7e4761162`
- R0Z MaskLayout `4f0615a66f8abe90b80d1cdff56961356cff13628c85dbd3456f43d9f425b43a`
- R0Z JointView `50d2b0075f4a8a9706d11b49b9da084e07a383fc1144a38cdc0e267530ecd64e`
- R0Z PayloadSplit `fca4444e9f8ebd1949a48d9bf71636beb5b80626459dbabcfc05173327a8e285`
- R0Z PureRounds at `700dd4b4`: `227c7f5886841b6678da2189cb0196f5d3f286b44887512a35468d54c4b704c4`
- R1 TranscriptView `bce7a74ce7e9ed7c16aa9248b4c808d45847d8e7c455457086f976b65c1b5798`
- R1 UnifiedSampler `ac0ed518595233c81a4b2c3f368bb20c513cb29b888f19dc586801a9ac0b98ad`
- R1 UnifiedRun `473377ddd83cf309745e1cad9ad9edc96cc256e70a9d4467144d15f80cc2b259`
- R1 UnifiedSemanticActualView `3ae47f0dcaf56385c9f9eb705364157b952e0a954b6dba27aa8d555d4ad37d8f`
- R1 UnifiedSemanticFacts `b5711a86f0c8e655b50fc759172194d7075c8bd3895b9e7054889a642db94c50`
- R1 UnifiedSemanticRecords `85e696dc5ddfbb1524cc6599257513fd6674149eac6697446a6c29f96375e50b`
- R1 UnifiedOpeningView `6b7930f94d7f48189162f58f9ccf3eedb165e56d3d3e50b93ac0cd09808e735f`
- R1 UnifiedQueryView `935609286d5b2e82b395e3c40f04bcb1a20bf1cbd39904805c9c610b9af20e79`
- R1 SemanticOpening `f9f72d9aaa478b6f751f0760291aced6c04a17ef6c8aebd48009b55406115d93`
- R1 InitialResponses `5a67cc4cb4db77f04e9f8f0d53c2d8ac1650f4fc01b130073c790bee89f3fd8d`
- R1 UnifiedInitialDecoder `ff8b18493918cc5a8d62a873c76117aece560062963ae7e5f036fd59cebaa7ec`
- R1 UnifiedInitialLaw `fdd839ffdcd0ef694abca3095ee39023f8ee18632a907cfa0bc1b379b4f70d69`
- R1 UnifiedPayloadStep `a4c579f794fe58946e2001c8228f60e85e139724e4f36dd2d9bd4c253d2b2359`
