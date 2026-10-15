# Semantic-field theorem reuse inventory

Pinned to repository HEAD a17829a776d533d7cd0beeb1f8676dcc793a909c. This is a source-anchored API inventory for field-domain reuse. It records theorem assumptions and direct import paths; it does not select a security premise or claim an instantiated gate is closed.

| Source | SHA-256 | Direct imports |
| --- | --- | --- |
| docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemRounds.lean | 564b9026233a36736f524407f357b44e173173139e52b9c4c6effbd88335bfd4 | R0P.SemClosed, R0P.SemBadSets, Mathlib.Tactic.LinearCombination, Mathlib.Tactic.Ring |
| docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD2.lean | 2b68437dfd6ba62cd023013a5b514987255550124c0eca4abb03a26a560397c0 | R0P.SemD3, R0C.ModuloField, R0C.ConcreteSlack |
| docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskBadSets.lean | 18b0499811001773be7ec5d2ff2e9463a2ff22048281595b76008033427862f7 | R0P.MaskView, R0P.MaskD2 |
| docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD3.lean | 68cd2542aff4f20ead2f5855663cf3e743817725f2714cc3400a21b0f651c74b | R0P.SemDecision, R0P.SemRounds, R0P.SemClosed |
| docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD3Glue.lean | 60830349937666ec050499c10bdb51e5c17811a949edd494f9205f0ee45ad852 | R0P.SemD2, R0P.CircleSampler, R0P.SemAccept, R0P.SemHonest, R0P.SemVirtualDeg, R0P.SemPad, R0C.V3.R0Q, R0P.MessageDescent, R0C.SemStatement, R0FS.Hypotheses |
| docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemBadSets.lean | b74e1d7adfaaf6ad0c4973b96461b6359d23b62d6cadb6e2983646d3e5b40b5d | R0P.Zerocheck and Mathlib finite-field/polynomial support |
| docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskD2.lean | 22af138da175023e657cd78ca98c15468b7c29ca166d5d14e3d02abb687e1041 | R0P.MaskProtocol, R0P.SemD2Glue, R0C.Counting |
| docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean | f27198834fa43256002cce83de7eeef675fecd88e89db0ee7a2bc00ef3a8b44b | R0P.MaskProtocol |

The three requested primary files are tracked in this worktree. Their transitive semantic dependencies include SemD3/SemClosed for the ordinary core and MaskD2/SemD2Glue for masked probability adapters.

## Field-parametric algebra and cardinality

SemRounds declares K with only [Field K] for its polynomial/round definitions. The exact root event alphaRound at lines 43-47 is over polynomials in K[X] and challenge x:K. alphaRound_card at lines 111-135 adds [Fintype K], a prover-polynomial degree bound, and proves a root-count bound d. It has no QM31 embedding or characteristic assumption.

The protocol-round event semRoundBad at lines 775-800 is also generic in K. Its additional data are F : Subfield K, PackBasis F, a trace/public object over K, and challenge prefix/current challenge in K. semRoundBad_card at lines 810-827 adds [Fintype K] and the explicit pre-challenge degree-check premise hchecked; it returns the per-round cardinality budget. No theorem there requires K to be QM31 or the challenge to lie in a named proper subfield. lambdaRoundBad_card and chiRoundBad_card at lines 324-368 and 398-444 likewise use [Fintype K] and the field structure, with respective cardinality bounds 2176 and 544.

SemD2 has a generic section at lines 34-175 with [Field K], [Fintype K], [DecidableEq K], [Algebra (ZMod P) K], and Sfield : Fin 29 → Subfield K. Its candidates/candidates_card and semanticBad/semanticBad_card declarations at lines 43-73 and 116-174 remain parameterized by K. semanticBad_card bounds the classified challenge set using the generic per-round root count and candidate cardinality. These APIs can be instantiated at K = WideExact if the listed instances and typed context are supplied; this statement is only about their types.

The D3 core is field-parametric too. SemD3.d3_core at SemD3.lean:88-112 takes generic K with [Field K], [Fintype K], [DecidableEq K], [Algebra (ZMod P) K], Sfield subfields, PackBasis, and an explicit [CharP K P] plus hP : P = 2^31 - 1. It consumes BaseTyped, HonestRows, VirtualDeg, ChecksAccept, sumcheck checks, and the per-round no-bad premise, then concludes ProductionHolds and CopyLinkBalance. The character/algebra premises are field assumptions; they do not force the semantic challenge value into an embedded QM31.

MaskBadSets also separates generic classification from the sampler adapter. Its alphaSomeBad definition at lines 17-20 and alphaSomeBad_card at lines 22-37 are generic over field K, with [Fintype K] and a degree bound for the count. semanticBadZ at lines 52-79 is generic over K with [Field K], [Fintype K], [DecidableEq K], [Algebra (ZMod P) K], Sfield subfields and PackBasis. Its classifier branches reuse generic semanticBad/alphaSomeBad predicates with the current challenge c:K. Thus the classifier itself admits the ordinary wide-field carrier at the level of declarations.

## Challenge law is narrower in the existing D2 adapters

SemD2 then specializes its one-block semantic sampler. qm31Rank at lines 180-184 maps Fin(P^4) into AspisV8R15.ExactTowerBase.QM31Exact; qm31Sample and qm31Sample_mass at lines 183-190 are typed at QM31Exact. semChal at lines 205-206 is defined as algebraMap QM31Exact WideExact applied to qm31Sample. semChal_mass, semChal_event, and semantic_round_density at lines 208-253 are therefore typed over WideExact, but their challenge distribution is supported on the algebraMap image of QM31Exact. The per-point mass uses the P^4 sampler bound and deltaQ = P^4 / 256^32; it is not a uniform-WideExact challenge law.

The masked adapter alphaSomeBad_semChal_mass in MaskBadSets.lean:81-94 is likewise specialized to SemE (WideExact) and the same semChal sampler. Its generic set cardinality result is field-parametric, while this mass theorem takes an event over candidates and bounds only after composing the event with the QM31-to-WideExact semChal.

So the source exposes a reusable distinction: algebraic bad-event classifiers/cardinality arguments accept K = WideExact under their explicit field/subfield/finite assumptions; the existing semantic sampler-density theorems still model embedded QM31 challenges, not an arbitrary sample from the full WideExact carrier. This inventory does not decide which distribution or premises belong in a later R1 argument.

## Fixed WideExact semantic wrapper

SemD3Glue.lean:528 defines SemE := WideExact, and the fixed WideExact wrappers below it construct the old semantic protocol/sampler using that carrier. SemD2Glue.lean directly imports SemD2, CircleSampler, SemD3Glue, DuplexDensity, CircleRows, and DuplexQ. MaskBadSets imports MaskD2, which imports MaskProtocol and SemD2Glue. These fixed wrappers are distinct from the generic K sections above.

The distinction is about theorem parameter types and sampler support only. It makes no statement about Rust transcript encoding, R1 statement equality, caller semantics, probability premises, or the applicability of an old masked D3 theorem to an R1 challenge schedule.
