# R1 Lean reuse inventory (working document)

Produced 2026-10-11 by a read-only Claude subagent from theorem *statements*
(no proofs read, nothing compiled), reviewed by the lead for its summary and
its error-term table; individual rows are the agent's classification and may
be revised when the R1 ledger is written. Classification codes: REUSE-AS-IS,
RE-INSTANCE (same theorem, new parameters), REWRITE, RETIRE, UNSURE.

# R1 reuse inventory of the R0 Lean development

2026-10-11. Read-only inventory, worktree `/Users/dominic/ZK/.worktrees/ZK-v8-reference`. I read statements, not proofs. I did not compile anything. All bit values were computed with `python3 -I`, using |E| = p^8 (2^248.00) and |K| = p^4 (2^124.00) with p = 2^31-1.

## Summary (10 lines)

1. I classified 212 modules: R0 25, Wide 53, R0FS 5, R0C 28, R0P 79, R0Z 21, plus the root `WideTower.lean`.
2. 120 modules (57%) are REUSE-AS-IS. This covers all of the semantic layer except its opening glue, the generic GS/Hensel machinery, the initial-code chain (F1, F3, joint list, subfield descent), the generic FS/duplex lemmas and the abstract ZK laws.
3. 32 more modules (15%) can be reused unchanged for fold 1 or for the unchanged query domain, but each needs a second copy for fold 2. 39 (18%) are RE-INSTANCE: same theorem with new ε, rounds, payload type or π := π_R1. 12 (6%) are REWRITE, 5 are RETIRE (the four Chord* files and `R0Z/QuotientImage`), and 4 are UNSURE (R0C/CircleCard, CircleRows, CircleSource and R0P/CircleSampler, which all depend on the OOD point domain).
4. Every transport use takes `π : Fin 1024 ≃ Fin 1024` as a parameter (`coeffWeight`, `rowsEquiv`, `LambdaRows`, `maskClaimsR0`, `PayloadSplit.L`). Only `R0Z/HonestView.D13Order` fixes D13, so π_R1 instantiates mechanically. The `π` in R0FS/R0C duplex files is the proof string, not the transport.
5. The fold-1 code (256 → 2^18, threshold 9557, `foldChallengeCap`) is exactly R0's final code. F2 (`Wide/Terminal`, `MatchedInstances`), F4 (`R0/Fold`) and F5 (`R0/Round`) therefore carry over to fold 1 as-is.
6. Largest new obligation (A): a second DegreeThreeCurveDecodable instance for a 64 → 2^16 line code. The entire Wide final chain hard-codes 256/255, 2^18, 9557/9558, Y-rows 113, Z-bound 12594 and `foldChallengeCap`. That means a new encoder, GRS conversion, interpolation and factor budgets, a new cap, and re-instances of Final{Root,Branch,Selection,CurveBranch,Curve}/Terminal/Matched. The generic Hensel layer assumes Y-degree < 113 (UNSURE whether the new instance satisfies it).
7. Largest new obligation (B): F4/F5/fibre restoration for the 4-to-1 fold on the line domain (2^18 → 2^16). `R0/Fold` is circle-fibre geometry, so it does not transfer. AspisFormal has `storedLine16X` (`V5FriReleasedLineGeometry`), but no Lean fold identity for this step exists in these trees. `RoundCore` hard-codes `Fin 1024`/`Fin 256`.
8. Largest new obligation (C): two-fold opening binding without the quotient. This replaces `OpeningDefinitions`/`Binding`/`BadSetBounds`/`Ledger`/`R0FS.Protocol`+`Hypotheses`. It needs: OOD as product-form functionals with an OOD collision (list-to-unique) bad set; B3 widened to 6 rows (100·6·28 = 16800); B4 at degree 6 (600); B7 twice; B6′ with a new cap; no B2/B5/τ. The R0C/R0P opening glue and the R0Z payload (`HonestView`, `PayloadSplit`, `Z4Maps`: final64, two opening polys, oracle openings, no `quotientLinear`) must then be re-threaded.
9. Over QM31 only two error terms fail 100 bits: γ (a_γ, 75.74 bits) and the fold challenge (a_f, 80.90 bits). R0's binding row is the 22-query term at 105.14 bits, field-independent. Every semantic term is ≥ 105.27 bits over |K|.
10. UNSURE items: whether OOD points stay circle points (this decides R0C/Circle*, `R0P/CircleSampler`, `ChordGeometry.Point`); the fold-2 agreement threshold and cap; whether queries remain uniform 22-subsets of 2^18 fibres (this decides `QueryLaw`, `Q22Law`, `QuerySampler` reuse); whether the total FS round count stays 32 (this decides the `MaskDuplex*` re-instance).

## Table 1. Module reuse map

Deps codes: **K** generic in the field; **E** specific to WideExact/E (has a `wide*` instance or WideExact in statements); **Q** uses the chord quotient, secant, `interpolant`, `virtual`, `quotient_from_final`, `L z0 z1`, `imageFunctional` or `BaseRational`; **F** uses the single 4-to-1 fold or the sizes `Fin 256`/`Fin 262144`/`Fin 1048576`/`childIndex`/`Fin 4` slots; **T** uses `transport`/`coeffWeight`/π (T(param) means π is an abstract argument); **W** uses width-29 batching (`width29Batch`, `Lambda`, lists); **FS** is FS/duplex framework only; **S** is semantic layer only (rows, terminal, mask); **P** is privacy payload. "Fold 2" means the second 4-to-1 fold 256 → 64 on 2^18 → 2^16.

| Module | Main theorems / definitions | Deps | R1 classification |
|---|---|---|---|
| **R0/** (wide-reference) | | | |
| R0/Audit | `#print axioms` list only | E Q F | REWRITE: new audit list (drop `Chord.F6`, `wideF6`, `interpolationLinear`; add second-fold/OOD theorems) |
| R0/BadSetBounds | `batch_union_bound`, `B2_card`≤5600, `B3_card`≤11200, `B4_card`≤400, `B5_card`≤200, `B7_card`≤600, `*_outside` | K Q W | Split. `batch_union_bound`, `B3_*` REUSE (B3 RE-INSTANCE with 2 more OOD rows: 100·6·28). `B2_*` (image functionals of `virtual`), `B5_*`/`imagePolynomial_*` RETIRE. `B4_*` RE-INSTANCE (pointPolynomial degree 4→6 with OOD at κ⁵,κ⁶). `B7_*` RE-INSTANCE twice (once per fold; `Close (batch D γ)` without quotient) |
| R0/Binding | `V1_iff_matching`, `quotient_from_final`, `recovered_*`, `tuple_descent`, `binding`, `wideBinding` | K E Q F T W | REWRITE: two-fold binding without quotient. `tuple_descent` REUSE as-is; `foldWord_curve` REUSE for fold 1 |
| R0/Chord | `L`, `no_domain_zero`, `interpolant`, `interpolationLinear`, `F6`, `wideF6`; also `evalMessage`, `domainPoint`, `BaseRational` | K E Q F(2^20) | RETIRE (quotient). Salvage `evalMessage` (circle-point evaluation of a message; the OOD functional) and `domainPoint` |
| R0/ChordDegree | `mulP0`, `mulP1`, `product_degree`, `bounded_product_iff` | K Q | RETIRE |
| R0/ChordGeometry | `secant*`, `secant_only_zeroes`, `Point`, `line` | K Q | RETIRE (keep `Point` if OOD points stay on the circle; UNSURE, see R0C/Circle*) |
| R0/ChordImage | `e1`, `e2`, `image_iff`, `quotientWeights`, `quotient_pairing`, `chordMessage` | K Q F | RETIRE |
| R0/CitedKernelAudit | `literal_cited_counterexample` | K F(256) | REUSE-AS-IS (historical gap-13 record; no R1 dependency) |
| R0/FibreRestoration | `restore`, `matched_close`, `fibreSet_card`, `join` | K F(Fin 4, 2^18→2^20, childIndex) | REUSE for fold 1; RE-INSTANCE for fold 2 on the line domain (2^16→2^18 fibres; different `childIndex` geometry) |
| R0/Fold | `F4`, `wideF4`, `foldWord`, `foldMessage`, `channels`, `fibre_inverse` | K E F(circle fibre, 2^18, 256) | REUSE for fold 1 (1024→256, circle). NEW for fold 2: line-code F4 (256→64, 2^18→2^16); no Lean analogue in these trees |
| R0/FunctionalWeights | `row`, `row_pairing` | K | REUSE-AS-IS (turns a functional into a weight vector: the OOD-as-weight step) |
| R0/KernelCorrespondence | `correspondence`, `firstFold_eq`, `dualFold_eq` | K F(256) | REUSE for fold 1; RE-INSTANCE for fold 2 only if a source kernel at 256→64 is cited (UNSURE) |
| R0/Ledger | `bad_set_cardinalities`, `grouped_cardinalities`, `wide_bad_set_cardinalities` | K E Q W | REWRITE (new bad-set list: B1, B3′, B4′, B6, B7, B6′, B7′, OOD) |
| R0/LinearDual | `dot`, `weights`, `transpose_pairing` | K | REUSE-AS-IS |
| R0/ListsResponses | `Close`, `Lambda`, `LambdaR`, `B1_card`≤a_γ, `B6_card`≤a_f, `gamma_match`, `alpha_match` | K F W | REUSE (Close, Lambda, B1, fold-1 B6). RE-INSTANCE `B6`/`AlphaValid`/`alpha_match` for fold 2 (new encoder, threshold, cap) |
| R0/OpeningAlgebra | `dot_*` lemmas, `total_pairing`, `image_functionals`, `imagePolynomial_eval`, `recovered` | K Q T W | REWRITE (keep `dot_*`, `pointDefect_eq`, `extraDefect_eq`; drop image/recovered) |
| R0/OpeningDefinitions | `Data`, `eqWeight`, `coeffWeight`, `virtual`, `batch`, `imageFunctional`, `weights`, `claimPrime`, `qWeights`, `totalWeights`, `B2..B7`, `V1`, `V2`, `Accept` | K Q F T W | REWRITE (no `virtual`/`interpolants`/`qWeights`/`imageFunctional`; `batch` = Σγ^l W_l; weights add OOD at κ⁵,κ⁶; V1/V2 per fold; final64). `eqWeight`, `indicator`, `coeffWeight*` REUSE with π := π_R1 |
| R0/PolynomialPair | `pair_complete`, `naturalLinear`, `p0Linear`, `p1Linear`, `polynomial_eq_of_fibres` | K | REUSE-AS-IS (useful for natural-basis OOD weights) |
| R0/ProtocolFields | `protocolField`, `protocolField_base/qm31`, `wideProtocolBinding` | E Q | REUSE `protocolField*`; REWRITE `wideProtocolBinding` (wraps `binding`) |
| R0/QueryLaw | `uniform_subset_bound`, `uniform_q22_bound` (M ⊆ Fin 262144, ≤9557) | F(2^18) | REUSE if queries stay uniform 22-subsets of the 2^18 fibres; RE-INSTANCE if the query domain/threshold changes (UNSURE until R1 ledger) |
| R0/ResponseSelection | `selected`, `selected_spec` | K | REUSE-AS-IS |
| R0/RootCounts | `badRoots`, `badRoots_card`, `union_bound` | K | REUSE-AS-IS |
| R0/Round | `F5`, `wideF5`, `boundary_claim` | K E F(1024→256) | REUSE for fold 1; RE-INSTANCE for fold 2 (256→64) |
| R0/RoundCore | `slot`, `unflatten`, `fold`, `dualFold`, `polynomial`, `eval_polynomial` (all `Fin 1024`/`Fin 256`) | K F | RE-INSTANCE: generalise to `Fin (4n) → Fin n` or add a 256→64 copy |
| R0/RoundNormalization | `roundPolynomial`, `citedDualFold`, `round_degree`, `round_eval`, `round_boundary`, counterexamples | K E F | REUSE for fold 1 (counterexamples as records); RE-INSTANCE round identities for fold 2 |
| **Wide/** | | | |
| Wide/Agreement | `exactInitialNormalizedLanes_curve`, `exactFinalLanes_curve`, `exactFinalValidCandidate_substitute_eq_zero` | K F W | REUSE (initial half, final half for fold 1); RE-INSTANCE final half for fold-2 code |
| Wide/AmbientCurve | `lagrangeAmbientCurve`, `candidate_eval_eq_lagrangeAmbientCurve_eval` | K | REUSE-AS-IS |
| Wide/BatchSeparation | `pairCollisions_card_le`, `exists_nonzero_injective_batch` | K W | REUSE-AS-IS |
| Wide/BranchEvaluation | `finiteBranchValue_eq_received_of_many_agreements` | K | REUSE-AS-IS |
| Wide/Cardinality | `card_fin_lt_of_budget` | K | REUSE-AS-IS |
| Wide/ConcreteBranch | `exists_exactFinal_components_of_fixed_branch`, `exists_exactInitial_components_of_fixed_branch` | K F(2^18,2^20,9557,38229,255) W | REUSE initial + fold-1 final; RE-INSTANCE final theorem for fold-2 code |
| Wide/DegreeThreeMatched | `degreeThree_bad_response_challenges_card_le`, `badStrategy`, `HasMatchingDecomposition` | K F(Fin 4 lanes) | REUSE-AS-IS (generic in encoder; fold-2 instance applies it) |
| Wide/EncoderConjugation | `map_initialEncoder` | K | REUSE-AS-IS |
| Wide/EncoderLinearity | `exactInitialEncoder_injective`, `exactFinalEncoder_add/smul`, `exactFinalMessageCurve` | K F W | REUSE; add fold-2 encoder linearity (RE-INSTANCE) |
| Wide/EncoderRegression | `initialEncoder_eq_v7`, `finalEncoder_eq_v7` | K | REUSE-AS-IS |
| Wide/FactorBudgets | `fixedBranchEvaluationBudget_le`, cap inequalities (lines 682–728) | K F | REUSE generic parts; RE-INSTANCE the final-code budget lemmas (693–728) for fold 2 |
| Wide/Factors | `curveTrivariatePolynomial`, `specializeChallenge`, `candidate_linearFactor_dvd_of_substitute_eq_zero` | K | REUSE-AS-IS |
| Wide/FinalBranch | `exists_exactV7Final_components_of_branchSelection` | K F | REUSE (fold 1); RE-INSTANCE (fold 2) |
| Wide/FinalCurve | `exists_exactV7Final_curve_of_valid_challenges` | K F | REUSE (fold 1); RE-INSTANCE (fold 2) |
| Wide/FinalCurveBranch | `exists_exactV7Final_components_of_selected_branch` | K F | REUSE (fold 1); RE-INSTANCE (fold 2) |
| Wide/FinalEncoder | `exactFinalEncoder`, `exactFinalEncoder_injective`, `exactInitialEncoder_eq_circleLift` | K F(256, 2^18 line, childIndex) | REUSE (fold-1 target code); NEW fold-2 encoder `Fin 64 → Fin 65536` (AspisFormal `V5FriReleasedLineGeometry.storedLine16X` exists; correspondence UNSURE) |
| Wide/FinalRoot | `exactFinal_challengeCandidateHom_eq_zero` | K F | REUSE (fold 1); RE-INSTANCE (fold 2) |
| Wide/FinalSelection | `exists_exactV7Final_weighted_fixed_branch` | K F | REUSE (fold 1); RE-INSTANCE (fold 2) |
| Wide/FiniteBranch | local-branch homs, `natDegree_localCoefficientPolynomialHom` | K | REUSE-AS-IS |
| Wide/FixedBranchCurve | `exists_ambient_curve_of_fixed_branch` | K | REUSE-AS-IS |
| Wide/FunctionField | `exactV7_localPrimeFactor_derivative_ne_zero` (hyp. natDegree < 113) | K | REUSE if the fold-2 GS instance keeps Y-degree ≤ 112 (UNSURE until its interpolation budget is fixed) |
| Wide/GRSConversion | `exactFinalGRSConversion`, `exactFinal9558_transport`, `exactInitial38230_transport` | K F(256, 2^18, 2^20) | REUSE; RE-INSTANCE final GRS conversion for the fold-2 code |
| Wide/Hensel | `exists_powerSeries_root_of_*` | K | REUSE-AS-IS |
| Wide/HenselCombinatorics | `henselDenominatorExponent`, `clear_hensel_product_denominators` | K | REUSE-AS-IS |
| Wide/HenselIntegralLift | `clearedTail`, `integralBranchIterated*` | K | REUSE-AS-IS |
| Wide/HenselRecurrence | `exactV7_fixedBranch_coefficient_recurrence` | K | REUSE-AS-IS |
| Wide/HenselSpecialization | `shiftedCandidateSeries`, `shiftedCandidateSeries_isRoot` | K | REUSE-AS-IS |
| Wide/HenselWeights | `integralBranchIteratedWeight_shiftedCoefficient_le` | K | REUSE-AS-IS |
| Wide/Initial | `exactV7InitialWidth29CurveDecodable` (38229, `initialBatchChallengeCap`) | K F(2^20) W | REUSE-AS-IS (γ over the unchanged initial code) |
| Wide/InitialBranch | `exists_exactV7Initial_components_of_branchSelection` | K F W | REUSE-AS-IS |
| Wide/InitialCurve | `exists_exactV7Initial_curve_of_valid_challenges` | K F W | REUSE-AS-IS |
| Wide/InitialCurveBranch | `exists_exactV7Initial_components_of_selected_branch` | K F W | REUSE-AS-IS |
| Wide/InitialEncoder | `exactInitialEncoder`, `exactInitialEncoder_overlap_cap` | K | REUSE-AS-IS |
| Wide/InitialRoot | `Width29GoodChallengePackage`, `exactInitial_challengeCandidateHom_eq_zero` | K W | REUSE-AS-IS |
| Wide/InitialSelection | `exists_exactV7Initial_weighted_fixed_branch` | K F W | REUSE-AS-IS |
| Wide/Instances | `wideInitialWidth29CurveDecodable`, `wideFinalDegreeThreeCurveDecodable`, `unchangedChallengeCaps` | E W F | REUSE; ADD `wideFold2DegreeThreeCurveDecodable` (new cap) |
| Wide/Interpolation | `exactInitialCurveInterpolationBudget`, final budget (`finalCurveYRows`=113, `finalCurveZBound`=12594) | K F | REUSE; RE-INSTANCE final budget for fold-2 code |
| Wide/JointList | `jointInitialList_card_le_100`, `wideJointInitialCodewords_card_le_100` | K E W | REUSE-AS-IS |
| Wide/LocalFactors | `bivariatePrimeFactors`, `exists_frequent_localPrimeFactor` | K | REUSE-AS-IS |
| Wide/MatchedInstances | `final_matchingDecomposition_iff`, `exactFinal_bad_response_challenges_card_le`, `wideFinal_bad_response_challenges_card_le` | K E F | REUSE (fold 1); RE-INSTANCE (fold 2) |
| Wide/MultiplicityThreeGS | `exactFinalInterpolationBudget`, `exactInitialInterpolationBudget`, `exactInitialCloseCandidate_card_lt_101` | K F | REUSE (initial list F3; fold-1); RE-INSTANCE final half if fold-2 needs a list bound (UNSURE whether R1 needs it) |
| Wide/OuterSelection | `exists_weighted_fixed_branch`, `zeroSpecializationChallengeSet_card_le` | K | REUSE-AS-IS |
| Wide/PowerSeriesLift | `exists_exactV7_fixedBranch_powerSeriesRoot` | K | REUSE-AS-IS |
| Wide/Regression | `qm31InitialWidth29CurveDecodable`, `initialResult_eq_v7` | K W | REUSE-AS-IS |
| Wide/RegularEvaluation | `regularizedBranchEvaluation` lemmas | K | REUSE-AS-IS |
| Wide/RegularHensel | `exactV7_regularizedHenselDerivative_ne_zero` | K | REUSE-AS-IS |
| Wide/RegularRing | `integralLocalFactor`, `integralBranchToFunctionField` | K | REUSE-AS-IS |
| Wide/RegularWeights | `localBivariateWeight*` | K | REUSE-AS-IS |
| Wide/RegularZeroCount | `card_rootPair_specializations_le`, `integralBranchToFunctionField_injective` | K | REUSE-AS-IS |
| Wide/ReleasedLift | `exists_exactInitial_components_of_ambient_curve`, `exists_exactFinal_components_of_ambient_curve` | K F W | REUSE; RE-INSTANCE final for fold 2 |
| Wide/Smooth | `separabilityCertificate`, `curvePrimeFactor_resultant_derivative_ne_zero` | K | REUSE-AS-IS |
| Wide/SubfieldDescent | `initialCodeword_subfield_descent`, `wideInitialCodeword_subfield_descent` | K E F(2^20) | REUSE-AS-IS |
| Wide/Terminal | `exactV7FinalDegreeThreeCurveDecodable` (9557, `foldChallengeCap`) | K F | REUSE (fold 1); RE-INSTANCE (fold 2: new threshold, cap) |
| WideTower.lean (root) | `WideExact`, `wideExact_card` | E | REUSE-AS-IS |
| **R0FS/** | | | |
| R0FS/Hypotheses | `rb0..rb4`, `d1`, `d2_round0..4`, `d2`, `d3`, `accept_not_doomed`, `readsChallenges` | K E Q F W | REWRITE (per-round D2/D3 for R1's rounds; structure reusable) |
| R0FS/Main | `r0_fiat_shamir`, `wide_r0_fiat_shamir` | E FS | RE-INSTANCE (R1 protocol object) |
| R0FS/Protocol | `Stmt` (z0,z1,BaseRational,transport), `Msg`, `Chal`, `Witness`, `bad0..bad4`, `roundBad`, `ε`, `SamplerLaws` | K Q F T W FS | REWRITE (new Msg: OOD values, v, P0, P1+oracle, F64; no τ; `ε` new) |
| R0FS/V2 | `r0_duplex_fiat_shamir`, `params1`, `SamplerLawsD`, `d3₂` | E FS | RE-INSTANCE (π here is the proof string, not transport) |
| R0FS/Verifier | `verifierFrom`, `verifier_readsChallenges`, `verifier_decision` | FS | REUSE-AS-IS (π = proof) |
| **R0C/** | | | |
| R0C/CircleCard | `split_circle_card`, `qm31_circle_card` | K Q(motivation) | UNSURE: REUSE if OOD points are circle points over K; RETIRE if z ∈ K is a line coordinate |
| R0C/CircleRows | `baseRational_card`, `z0_density_le`, `z1_density_le`, `chord_conditions` | K Q | RE-INSTANCE/REWRITE: the rational/equal exclusion exists for L; R1 needs an OOD collision row instead (UNSURE) |
| R0C/CircleSource | `distinct_success_conditions` | Q FS | as R0C/CircleRows (UNSURE) |
| R0C/ConcreteSlack | `gamma_mass`, `ordinary_mass`, `query_success_mass` | E F(2^18) | REUSE field clauses; query clause REUSE iff query domain unchanged |
| R0C/Counting | `uniform_of_point_mass_le`, `mean_or_eq_le` | K | REUSE-AS-IS |
| R0C/ModuloCounting | `encoded_mass_le`, `event_mass_le` | K | REUSE-AS-IS |
| R0C/ModuloField | `gamma`, `ordinary`, `gamma_mass_257`, `ordinary_mass_257` | E FS | REUSE-AS-IS (E samplers) |
| R0C/OpeningSamplerBounds | `gamma_bad_density`, `kappa_bad_density`, `tau_bad_density`, `alpha_bad_density`, `query_budget` | E F W | RE-INSTANCE (new bad-set counts; drop τ; add α₁) |
| R0C/QueryCounting | `ordered_card`, `subset_mean` | K | REUSE-AS-IS |
| R0C/QuerySampler | `sampler`, `sampler_subset_le`, `querySet` (2^18) | F FS | REUSE iff queries stay on 2^18 fibres (UNSURE) |
| R0C/QuerySource | `successful_subset_le`, `initialLegal` | F FS | as QuerySampler |
| R0C/SamplerObstruction | `noSamplerLawsD` | E FS | REUSE-AS-IS (refutation record) |
| R0C/Sampling | `gamma`, `ordinary`, `queries`, `σ` | E F FS | REUSE iff query domain unchanged |
| R0C/SemStatement | `SourceData`, `z0Bad`, `z1Bad`, `rowBudget`, `SemanticDensity`, `Obligations` | E Q(z rows) S FS | RE-INSTANCE (z rows → OOD rows; tail = R1 ε) |
| R0C/SlackBits | `bad_query_count`, `row_le_query`, `max_error_formula` | E F | RE-INSTANCE (new ε rows; max still query row?) |
| R0C/SlackDensity | `d2_round0..4`, `d2` | E W FS | RE-INSTANCE |
| R0C/SlackDuplex | `r0_duplex_fiat_shamir_slack_of_laws` | E FS | RE-INSTANCE |
| R0C/SlackObstruction | `noSamplerLawsSlackD`, `query_count` | E F FS | REUSE-AS-IS (record) |
| R0C/SlackStatement | `SamplerLawsSlack`, `epsilonSlack`, `delta0` | E F FS | RE-INSTANCE (new ε; `delta0` REUSE) |
| R0C/V3/BS | `BS`, `blaw`, `chainB` | FS | REUSE-AS-IS |
| R0C/V3/BSOk | `bfollow_ok`, `blaw_split`, `pmean_le` | FS | REUSE-AS-IS |
| R0C/V3/DQChain | `runOut_chainBS`, `chainS_reads` | FS | REUSE-AS-IS (generic chain) |
| R0C/V3/DQDecodes | `decodesQ`, `chainQ_4`, `chalQ_4` | FS | RE-INSTANCE if R1 opening is not "4 field challenges + 1 set" (R1 γ,κ,α₀,α₁,S keeps that shape; UNSURE) |
| R0C/V3/DuplexQ | `σQ`, `protocolQ`, `round_field_bound`, `round_q22_bound` | E F W FS | RE-INSTANCE |
| R0C/V3/DuplexQDensity | `chainDensityQ` | E FS | RE-INSTANCE |
| R0C/V3/Gen | `theorem43`, `lemmaA3`, `lemmaB3` | FS | REUSE-AS-IS |
| R0C/V3/Q22Law | `q22_bound`, `chainE_scanOut` | F FS | REUSE iff query domain 2^18 |
| R0C/V3/R0Q | `r0_q22_fiat_shamir`, `r0_q22_fiat_shamir_closed` | E F FS | RE-INSTANCE |
| **R0P/** (semantic proof) | | | |
| R0P/Asset | `assetFamily`, `asset_holds_iff` | S | REUSE-AS-IS |
| R0P/CircleSampler | `circleSampleParameter*_not_rational`, `circleFallback*` | E Q S FS | UNSURE (see R0C/Circle*): REUSE if OOD points are circle samples; non-rationality lemmas then unnecessary |
| R0P/Copy | `copyFamily`, `copy_positivity_links` | S | REUSE-AS-IS |
| R0P/CopyConstants | `copyPatterns`, `copyLink` | S | REUSE-AS-IS |
| R0P/CopyInputLinks | `copy_link_balance_pattern_funcs` | S | REUSE-AS-IS |
| R0P/CopyRegistry | `copyProducerRowSlots*` | S | REUSE-AS-IS |
| R0P/Core | `Trace`, `Openings`, `Public`, `Family`, `Holds` | S | REUSE-AS-IS |
| R0P/CoreExt | `CFamily`, `PackBasis`, `pack4` | S | REUSE-AS-IS |
| R0P/Digest | `digestFamily`, `digest_holds_calls` | S | REUSE-AS-IS |
| R0P/EmptyRoots | `emptyRootsNat` | S | REUSE-AS-IS |
| R0P/Extraction | `extraction_*` | S | REUSE-AS-IS |
| R0P/LaneMap | `rowOf_bijective`, `lane_*_mem` | S | REUSE-AS-IS |
| R0P/LogUpAssembly | `BadLogUp`, `logup_step_of` | S | REUSE-AS-IS |
| R0P/LogUpChain | copy-link activity checks | S | REUSE-AS-IS |
| R0P/LogUpCompress | `compressPoly_*` | S | REUSE-AS-IS |
| R0P/LogUpFrac | `numer_partial_fraction` | K | REUSE-AS-IS |
| R0P/MaskAll | aggregator imports | S FS | RE-INSTANCE (import list) |
| R0P/MaskBadSets | `alphaSomeBad_card`, `semanticBadZ` | S T(param) | REUSE-AS-IS (π abstract) |
| R0P/MaskD2 | `etaBad_card`, `etaSomeBad_card`, `combinedD2BudgetZ` | E S FS | REUSE eta lemmas; RE-INSTANCE `combinedD2BudgetZ` tail (lines 153–155) |
| R0P/MaskD2Glue | `semantic_rowZ_D2`, `circle_row25_D2`, `circle_row26_D2` | E S FS | RE-INSTANCE (circle/OOD rows) |
| R0P/MaskD2Instance | `combinedProtocolZ_D2` | E FS | RE-INSTANCE |
| R0P/MaskD3Glue | `accepted_no_hit_extractedZ`, `d3Z` | E T W S FS P | RE-INSTANCE (opening decision glue) |
| R0P/MaskDensity | `semantic_round_densityZ` | S FS | REUSE-AS-IS |
| R0P/MaskDuplexChain | `combinedChainS_reads` | FS | RE-INSTANCE iff total round count ≠ 32 (else REUSE) |
| R0P/MaskDuplexDecoder | `combinedDec`, `combinedChainBS_31` | FS | as MaskDuplexChain |
| R0P/MaskDuplexDecodes | `combinedDecodes` | FS | as MaskDuplexChain |
| R0P/MaskDuplexDensity | `combinedChainDensity_of_D2` | FS | as MaskDuplexChain |
| R0P/MaskEarly | `earlyRounds_cover`, `no_hit_early` | S | REUSE-AS-IS |
| R0P/MaskFiatShamir | `combined_fiat_shamirZ` | E FS | RE-INSTANCE |
| R0P/MaskInstance | `masked_opening_budget_exact`, `combined_fiat_shamir_masked` | E F FS | RE-INSTANCE (new ε, query constant) |
| R0P/MaskMaxErr | `combined_maxErrWithEta`, `combined_maxErrZ`, `combined_fiat_shamirZ_closed` | E F S FS | RE-INSTANCE |
| R0P/MaskNoHit | `no_hit_eta`, `no_hit_alpha` | S | REUSE-AS-IS |
| R0P/MaskOpeningDensity | `opening_fieldZ_D2`, `opening_q22Z_D2` | E F FS P | RE-INSTANCE |
| R0P/MaskPrefix | `candidate_memZ` | S | REUSE-AS-IS |
| R0P/MaskProtocol | `combinedProtocolZ`, `terminalZ`, `openingParamsAt`, `combinedSamplerAt` | S FS T(param) | RE-INSTANCE (opening params/samplers) |
| R0P/MaskSemantics | `honestRowsZ`, `semantic_of_total_zero` | S T(param) | REUSE-AS-IS (π abstract; instantiate π_R1) |
| R0P/MaskSource | `sourceDataZ`, `combinedD1Z`, `opening_head_at_27` | S FS | RE-INSTANCE |
| R0P/MaskValue | `maskValue`, `libraTail`, `dot_libraWeight`, `maskClaimsR0` | S T(param) | REUSE-AS-IS |
| R0P/MaskView | `openingViewZ`, `semChalsZ`, `openingRoundsZ` | S FS | RE-INSTANCE (opening view targets R1 Stmt) |
| R0P/MessageDescent | `initialMessage_subfield_descent` | K | REUSE-AS-IS |
| R0P/Occupancy | `occupancy_holds_iff` | S | REUSE-AS-IS |
| R0P/Path | `pathFamily`, `path_holds_iff` | S | REUSE-AS-IS |
| R0P/Poseidon | `poseidonPermutation`, `poseidon_packing_kernel` | S | REUSE-AS-IS |
| R0P/PoseidonConstants | constants | S | REUSE-AS-IS |
| R0P/Positive | `positive_holds_iff` | S | REUSE-AS-IS |
| R0P/Positivity | `positivity` | S | REUSE-AS-IS |
| R0P/PositivityChain | `positivity_of_balance` | S | REUSE-AS-IS |
| R0P/PositivityWired | `positivity_of_families` | S | REUSE-AS-IS |
| R0P/Schedule | `scheduleFamily` | S | REUSE-AS-IS |
| R0P/SemAccept | `accept_of_checks` | S | REUSE-AS-IS |
| R0P/SemAll | aggregator imports | S FS | RE-INSTANCE (import list) |
| R0P/SemAssembly | `semantic_sound`, `semantic_extraction` | S | REUSE-AS-IS |
| R0P/SemBadSets | `sumcheck_rounds_bad`, `zerocheck_bad` | K S | REUSE-AS-IS |
| R0P/SemBridge | `weighted_witness_degree` | S | REUSE-AS-IS |
| R0P/SemCharP | `semE_charP` | E | REUSE-AS-IS |
| R0P/SemClosed | `semantic_sound_closed`, `semantic_extraction_closed` | S | REUSE-AS-IS |
| R0P/SemD2 | `candidates_card`≤100, `semanticBad_card`, `semantic_round_density`, `deltaQ` | S T(param) W | REUSE-AS-IS (π abstract via `LambdaRows`) |
| R0P/SemD2Glue | `semantic_row_D2`, `opening_field_row_D2`, `opening_q22_row_D2`, `circle_row24/25_D2`, `combinedD2Budget` | E S FS P | RE-INSTANCE (opening and circle rows; semantic rows unchanged) |
| R0P/SemD3 | `d3_core`, `HonestRows`, `virtualPoly` ("virtual" = semantic, not the chord) | S | REUSE-AS-IS |
| R0P/SemD3Glue | `sourceData`, `duplexRows`, `openingView_semantic_head`, d3 glue to `R0FS.decision` | E Q(z cond.) T W S FS P | REWRITE (opening glue; semantic-head lemmas reusable) |
| R0P/SemDecision | `decision` (composes `R0FS.decision`), `terminalValue`, `sumcheckChecks` | S | RE-INSTANCE `decision`/`cardOK` (lines 112–126); rest REUSE |
| R0P/SemDeg | `VDeg`, `rowCodeEquiv` | S | REUSE-AS-IS |
| R0P/SemDegFamilies | `ldeg_*` | S | REUSE-AS-IS |
| R0P/SemDuplexDecoder | `combinedDec` (unmasked 31-round) | FS | RE-INSTANCE or RETIRE (superseded by Mask*; UNSURE whether still cited) |
| R0P/SemDuplexDecodes | `combinedDecodes`, `combinedChain_30` | FS | as SemDuplexDecoder |
| R0P/SemDuplexDensity | `combinedChainDensity` | FS | as SemDuplexDecoder |
| R0P/SemFiatShamir | `combined_fiat_shamir` | FS | as SemDuplexDecoder |
| R0P/SemHonest | `honestRows`, `honestClaims_ofBool` | S | REUSE-AS-IS |
| R0P/SemLedger | `causal_sum`=303000, `causal_le_two_pow_neg_105` | S | REUSE-AS-IS |
| R0P/SemMaxErr | `semantic_numeric_bound`, `combined_maxErr`, `combined_fiat_shamir_closed` | E F S FS | RE-INSTANCE (comparisons against new query row) |
| R0P/SemPad | `mem_Lambda_pad`, `padAgreement_lane26/27` | W T(param) S | REUSE-AS-IS |
| R0P/SemRounds | `semRoundBudget`, `lambdaRoundBad_card`≤2176, `alphaRound_card` | S | REUSE-AS-IS |
| R0P/SemSource | `Context`, `paymentWitness`, `d1_of_sourceData` | S | REUSE-AS-IS |
| R0P/SemView | `rowsEquiv`, `coeffsOf`, `LambdaRows`, `libraWeight`, `TypedContext`, `openingStmt`, `openingView` | Q(z) T W S | Split: `rowsEquiv`/`coeffsOf`/`LambdaRows`/`libraWeight` REUSE with π := π_R1; `openingStmt`/`openingView` REWRITE (R1 Stmt, no BaseRational) |
| R0P/SemVirtualDeg | `virtualDeg` (semantic) | S | REUSE-AS-IS |
| R0P/Semantics | `merkleRoot`, `noteCommitment`, `nullifierHash` | S | REUSE-AS-IS |
| R0P/Sumcheck | `bsum`, `badAlpha`, `sound` | K | REUSE-AS-IS |
| R0P/Value | `valueFamily`, `value_holds_iff` | S | REUSE-AS-IS |
| R0P/Zerocheck | `eqwB`, `mle`, `compose` | K | REUSE-AS-IS |
| **R0Z/** (privacy) | | | |
| R0Z/AbsorptionLaw | `law_product_right`, `uniform_coset` | K | REUSE-AS-IS |
| R0Z/AffineLaw | `equal_laws_of_mask_image`, `marginalisation` | K | REUSE-AS-IS |
| R0Z/D11Obstruction | `sparse_copy_not_separated` | S P | REUSE-AS-IS (record) |
| R0Z/D12 | `decomposition`, `payload_law`, `hvzk_perfect_of_maskImage` | T(param) P | RE-INSTANCE (new payload type; proof shape reusable) |
| R0Z/FsStatement | `ZK_FS`, `zkfs_of_hvzk_perfect` | FS P | REUSE-AS-IS |
| R0Z/HelperInvariant | `check_spec`, `before_*`, `after_*` | S | REUSE-AS-IS |
| R0Z/HonestView | `D13Order`, `Challenges`, `PayloadCell` (`openingCoeff (Fin 7)`, `finalCoeff (Fin 256)`, `opened (Fin 262144)(Fin 4)(Fin 29)`, `ood`), `quotientLinear`, `foldLinear`, `run`, `run_eq_payloadAffine` | Q F T P | REWRITE (two opening polys, folded-oracle openings, `finalCoeff (Fin 64)`, no quotient; `D13Order` replaced by explicit π_R1) |
| R0Z/Hvzk | `hvzk_perfect_of_maskImage`, `hvzk_zero_of_maskImage` | S P | REUSE-AS-IS |
| R0Z/JointTrace | `actual_affine`, `tapeLinear_pure` | S P | REUSE-AS-IS |
| R0Z/JointView | `HVZK_perfect`, `view_eq_z3` | P | REUSE-AS-IS (abstract) |
| R0Z/KernelImage | `surjective` | K | REUSE-AS-IS |
| R0Z/LawTransport | `mean_eq_of_equalLaws` ("transport" = law transport) | K | REUSE-AS-IS |
| R0Z/MaskLayout | `eligible`, `applyMask`, `traceAffine` | S | REUSE-AS-IS |
| R0Z/MaskedProtocol | `terminalZ`, `sumcheckChecksZ`, `maskValue_mldeg` | S | REUSE-AS-IS |
| R0Z/Partition | `pureTrace_fixed`, `extension_pure_zero` | S P | REUSE-AS-IS |
| R0Z/PayloadSplit | `L`, `O`, `run_split_*` (one per payload cell), `M_pure` | F T P | REWRITE (per-cell split for the R1 payload) |
| R0Z/QuotientImage | `quotient_mem_image`, `quotientLinear_unique_preimage`, `chordOnKernel` | E Q P | RETIRE |
| R0Z/StatisticalDistance | `dist`, `EqualLaws`, `dist_triangle` | K | REUSE-AS-IS |
| R0Z/ViewAffine | `originalAt_affine`, `terminalValue_eq_originalAt` | S | REUSE-AS-IS |
| R0Z/Z4Maps | `roundMaskMap`, `c1Map`, `c1_surjectivity` (Fin 262144 × Fin 4 cells) | F T P | RE-INSTANCE (π := π_R1; C1 cells over the R1 query layout) |
| R0Z/ZkStatement | `HVZK`, `ZK_FS`, `R0Obligations`, `messages` (Fin 32) | FS P | RE-INSTANCE (R1 message list/payload) |

## Table 2. Soundness error terms

Bits are −log2(term). "Count" means the numerator is a field-independent degree or list cap, so the term scales as count/|field|. The query term is field-independent outright. The Lean opening ε (`R0FS/Protocol.lean` `def ε`) is what the FS theorems use. Paper values (R0_SOUNDNESS §5–6) are listed where they differ: the Lean values include the D14″ fourth (Libra) row.

| Round / term | Constant (exact) | Denominator | Source theorem | Bits over E | Bits over QM31 | Field-independent count? |
|---|---|---|---|---:|---:|---|
| **Opening layer, R0FS ε** | | | | | | |
| ε0 γ: B1 ∪ B2 ∪ B3 (Lean) | 336869026605739 + 16800 = 336869026622539 | \|E\|−1 | `R0FS.ε 0`; `Ledger.grouped_cardinalities`; `MaskInstance.masked_opening_budget_exact` | 199.74 | 75.74 | count |
| ↳ B1 (F1, unmatched γ responses) | 336869026605739 = `initialBatchChallengeCap` | \|E\|−1 | `ListsResponses.B1_card`; `Wide/Instances.unchangedChallengeCaps`; cap check `FactorBudgets:682` | 199.74 | 75.74 | count. R1: unchanged |
| ↳ B2 (image functionals, 100·2·28) | 5600 | \|E\|−1 | `BadSetBounds.B2_card` | 235.55 | 111.55 | count. R1: RETIRE |
| ↳ B3 (point + extra claims, 100·4·28) | 11200 (paper: 8400 = 100·3·28) | \|E\|−1 | `BadSetBounds.B3_card` | 234.55 (paper 234.96) | 110.55 | count. R1: 100·6·28 = 16800 if OOD joins as 2 rows (estimate) |
| γ (paper §6) | 336869026605739 + 14000 | \|E\|−1 | R0_SOUNDNESS §6 | 199.74 | 75.74 | count |
| ε1 κ: B4 (100·4) | 400 (paper: 300) | \|E\| | `R0FS.ε 1`; `BadSetBounds.B4_card` | 239.36 (paper 239.77) | 115.36 | count. R1: 100·6 = 600 with κ⁵,κ⁶ OOD (estimate: 238.77 / 114.77) |
| ε2 τ: B5 (100·2) | 200 | \|E\| | `R0FS.ε 2`; `BadSetBounds.B5_card` | 240.36 | 116.36 | count. R1: RETIRE (no τ) |
| ε3 α0: B6 ∪ B7 | 9396508281246 + 600 = 9396508281846 | \|E\| | `R0FS.ε 3`; `Ledger.grouped_cardinalities` | 204.90 | 80.90 | count |
| ↳ B6 (F2 matched, a_f) | 9396508281246 = `foldChallengeCap` | \|E\| | `ListsResponses.B6_card`; `MatchedInstances.wideFinal_bad_response_challenges_card_le`; cap check `FactorBudgets:693`, `Terminal:116` | 204.90 | 80.90 | count. R1 fold 1: unchanged; fold 2: new cap (UNSURE) |
| ↳ B7 (round polynomial, 100·6) | 600 | \|E\| | `BadSetBounds.B7_card` | 238.77 | 114.77 | count. R1: once per fold |
| ε4 queries q=22 | C(9557,22)/C(262144,22); C(9557,22) = 3204816658150512709790016143025871214703406297554365823658832464480 | binomial | `R0FS.ε 4`; `QueryLaw.uniform_q22_bound`; `R0C.V3.Q22.q22_bound`; `SlackBits.bad_query_count` | 105.14 | 105.14 | field-independent |
| queries q=24 (paper) | C(9557,24)/C(262144,24) | binomial | R0_SOUNDNESS §6 | 114.70 | 114.70 | field-independent |
| E-sampler slack factor (1+δ0) | δ0 = 257·p^8/256^32 − 1 ≈ 0.0039062 | — | `SlackStatement.delta0`; `ConcreteSlack.gamma_budget`; `SlackBits.max_error_formula` | −0.0056 bits on every opening row; query row 105.136 | n/a | — |
| Sum of opening rows (Lean ε, q=22) | — | — | — | 105.14 (query-dominated) | — | — |
| **Semantic layer (K-valued challenges)** | | | | | | |
| SEM premise (V7 inventory) | 396430 | \|K\|−1 | R0_SOUNDNESS §6; `R0C/SemStatement.rowBudget`, `SemanticDensity` | (229.40) | 105.40 | count |
| Pair-forest SEM ledger, total | 303000 = 100·3030 | \|K\|−1 | `R0P/SemLedger.causal_sum`, `causal_le_two_pow_neg_105` | — | 105.79 | count |
| λ (tuple compression, 100·2176) | 217600 | p^4·(1+δQ)⁻¹ | `SemRounds.lambdaRoundBad_card`; `semRoundBudget 0`; `SemD2Glue.combinedD2Budget` | — | 106.27 | count |
| χ (active pole 273 + copy χ 271, ×100) | 54400 | p^4 | `semRoundBudget 1` | — | 108.27 | count |
| θ (29-lane row, 100·28) | 2800 | p^4 | `semRoundBudget 2` | — | 112.55 | count |
| zc, 10 coordinates (100·1 each) | 100 each | p^4 | `semRoundBudget 3..12` | — | 117.36 each | count |
| μ (100·2) | 200 | p^4 | `semRoundBudget 13` | — | 116.36 | count |
| Sumcheck α rounds, 10 (100·27) | 2700 each | p^4 | `semRoundBudget 14..23`; masked: `MaskD2.combinedD2BudgetZ` i=15..24, `MaskBadSets.alphaSomeBad_card` | — | 112.60 each | count |
| Mask η (100·1) | 100 | p^4 | `MaskD2.combinedD2BudgetZ` i=14; `etaSomeBad_card` | — | 117.36 | count |
| Circle rounds B2 z0, z1 (masked) | 2 each | p^4 | `MaskD2.combinedD2BudgetZ` i=25,26; `R0C/SemStatement.rowBudget`; `CircleRows.z0_density_le` | — | 123.00 each | count. R1: replaced by an OOD collision row, est. 100·1023/\|K\| = 107.36 (PLAN figure; UNSURE) |
| Circle rounds, unmasked variant | 1 each (×(1+δQ)) | p^4 | `SemD2Glue.combinedD2Budget` i=24,25 | — | 124.00 each | count |
| QM31 sampler slack δQ | p^4/256^32 ≈ 2^−132 | — | `SemD2.deltaQ`, `deltaQ_small` | — | negligible | — |
| Max semantic row vs query row | 2·217600 / p^4 ≤ query row | p^4 | `SemMaxErr.semantic_numeric_bound`; `MaskMaxErr.combined_maxErrZ` (max = query row) | — | 105.27 | — |
| **R1 rows (not in Lean; for the lead's ledger)** | | | | | | |
| Query term with threshold 2389 on 2^16 (hypothetical fold-2 analogue) | C(2389,22)/C(65536,22) | binomial | none | 105.25 | 105.25 | field-independent; UNSURE (threshold not fixed) |
| Same 9557 threshold but drawn on 2^16 (counter-check) | C(9557,22)/C(65536,22) | binomial | none | 61.14 | 61.14 | shows the domain choice matters |

## Table 3. Hard-coded parameters touched by a second fold / final64 / domain change

The token search covered `256`, `255` (final degree), `262144`/`2^18`, `1048576`/`2^20`, `9557`, `9558`, `38229`, `38230`, `foldChallengeCap`/`9396508281246`, `initialBatchChallengeCap`/`336869026605739`, `Fin 4`, `childIndex`/`parentIndex`/`slotIndex`, and fold-slot names (`slot`, `unflatten`, `channels`, `coefficientLane`, `fibreSet`, `fibreTransform`, `join`).

"Statement" counts theorem signatures plus `def`/`structure`/`abbrev` bodies. "Proof" means text after `:=` in a theorem. Comments, `#print` and `set_option maxRecDepth 262144/1048576` lines are excluded (26 option lines in Wide/*). Some files were removed as false positives after inspection: semantic `slot`/`Fin 4`/`256`/`2^20` in R0P Copy, CopyConstants, CopyRegistry, LogUpChain, Poseidon, PoseidonConstants, Value, Positivity, PositivityWired, CoreExt, MaskValue, LaneMap, SemDeg, SemDegFamilies and SemBridge; byte base `256^i` and `Fin 4` limb split in R0C/ModuloField; and `Fin 4` tower/extension coordinates in R0Z/MaskLayout and Partition.

In the R0P Mask*/Sem*Glue/SemMaxErr rows, `Fin 4` is the index of the **four opening field challenges** (`hσopen : ∀ j : Fin 4`), not fold slots. It changes only if R1's opening has a different number of field challenges. R1 (γ, κ, α0, α1) keeps four.

Definitions outside the trees: `foldChallengeCap`, `initialBatchChallengeCap`, `foldCurveDegree` = 3 and `initialBatchCurveDegree` = 28 are defined in `AspisFormal/AspisFormal/V6PublishedTheoremInterfaces.lean:37–41`. `finalCurveYRows` = 113, `finalCurveZBound` = 12594 and `finalCurveXBound` = 28674 are in `Wide/Interpolation.lean:580–582` (mirrored in `AspisFormal/K1/V7ExactCorrelatedAgreementInterpolation.lean:576–578`). `yDegree` = 112, `finalWeightedDegree` = 28673 and `initialWeightedDegree` = 114689 are in `Wide/MultiplicityThreeGS.lean:56–59`.

| File (tree-relative) | In statements / definitions (token: lines) | In proofs (token: lines) |
|---|---|---|
| R0/Binding.lean | `262144` 26,31,123; `slot` 32,41,127; `9558` 40,128 | `slot` 44; `9558` 45; `9557` 45; `38230` 75,143,144; `38229` 144 |
| R0/Chord.lean | `1048576` 18,22,29 | — |
| R0/ChordImage.lean | `1048576` 21,22,27; `262144` 33,36; `childIndex` 34,37 | `262144` 49; `childIndex` 51,52 |
| R0/CitedKernelAudit.lean | `256` 13,19,20,34,35; `Fin4` 13 | `256` 21,24,27,28 |
| R0/FibreRestoration.lean | `Fin4` 18,21,28,43,55,74; `slot` 18,21,29,40,49,56,57,75; `256` 21; `childIndex` 41,43; `262144` 40,43,49,55,73; `1048576` 40; `9558` 73 | `Fin4` 24,52; `slot` 36,50,63,65,68,78,80,85; `256` 25; `childIndex` 36,46 |
| R0/Fold.lean | `childIndex` 56; `262144` 18,55,58,61,65,74,87; `Fin4` 55,58,61,65,95,109; `slot` 58,61,65,66,69,75,89,96,110,113; `256` 72,89,96,110 | `childIndex` 21,22,24; `Fin4` 20,30,39,44,53; `slot` 75,76,98,113,114 |
| R0/KernelCorrespondence.lean | `256` 16,19,24,29,34,35,37,40; `slot` 16,19,24,29,34,35,37,40 | `slot` 26 |
| R0/Ledger.lean | `initCap` 15,25; `foldCap` 18,27; `slot` 18,27 | `slot` 33 |
| R0/ListsResponses.lean | `38230` 23,27,37,39; `1048576` 65,68; `262144` 66,70; `38229` 74; `Fin4` 78,80,96,103,109,128,157,159; `9557` 79; `initCap` 112; `foldCap` 128 | `1048576` 116; `262144` 132; `38229` 118,119,125; `9557` 134,135; `initCap` 125 |
| R0/OpeningDefinitions.lean | `262144` 143,146,154 | — |
| R0/QueryLaw.lean | `262144` 14,17,25,26,28,29,30,31,41,42; `9557` 29,31,41,42 | `262144` 32 |
| R0/RoundCore.lean | `256` 13,14,16,18,21; `Fin4` 13,14,17,19,21; `slot` 13,14,17,19,22 | — |
| R0/RoundNormalization.lean | `256` 25,32,36,94; `Fin4` 26,32,37,94; `childIndex` 26,34,37,94,95 | `256` 73,74; `Fin4` 39,73; `childIndex` 73,99,111,114 |
| R0C/ConcreteSlack.lean | `262144` 45,48 | `262144` 50 |
| R0C/OpeningSamplerBounds.lean | `initCap` 30; `foldCap` 50; `262144` 63; `9557` 63 | `initCap` 31; `foldCap` 51; `slot` 56; `262144` 67,68; `9557` 68 |
| R0C/QuerySampler.lean | `262144` 34,35,64,68,76,79 | — |
| R0C/QuerySource.lean | `262144` 18,21,23,25,38,41,76,79 | `262144` 45,60 |
| R0C/Sampling.lean | `262144` 36,38,42,44 | — |
| R0C/SlackBits.lean | `9557` 12,42; `262144` 42 | `9557` 35; `262144` 35 |
| R0C/SlackDensity.lean | — | `initCap` 49,53; `foldCap` 128,135; `slot` 133; `9557` 156,169; `262144` 166,169 |
| R0C/SlackObstruction.lean | `262144` 23,28 | — |
| R0C/SlackStatement.lean | `262144` 28,31 | — |
| R0C/V3/DuplexQ.lean | — | `initCap` 175,179,180,182,183; `foldCap` 237,240; `262144` 260; `9557` 260,267 |
| R0C/V3/Q22Law.lean | `262144` 91,97,116,119; `9557` 116,119 | `262144` 108,120,127,128; `9557` 128 |
| R0C/V3/R0Q.lean | `262144` 162; `9557` 162 | — |
| R0FS/Hypotheses.lean | `262144` 454 | `initCap` 212,216; `foldCap` 295,302; `slot` 300; `9557` 324,337; `262144` 334,337; `9558` 443,470 |
| R0FS/Protocol.lean | `262144` 63,101,174,199,202; `slot` 98; `9557` 102,174; `initCap` 170; `foldCap` 173 | — |
| R0P/MaskD2Instance.lean | `Fin4` 21 | `Fin4` 45 |
| R0P/MaskFiatShamir.lean | `Fin4` 128 | — |
| R0P/MaskInstance.lean | `initCap` 39; `Fin4` 50; `262144` 58; `9557` 58 | — |
| R0P/MaskMaxErr.lean | `Fin4` 119; `262144` 127; `9557` 127 | — |
| R0P/MaskOpeningDensity.lean | `Fin4` 31 | — |
| R0P/MessageDescent.lean | — | `1048576` 24 |
| R0P/SemD2Glue.lean | `Fin4` 360,1182,1441 | `Fin4` 1475 |
| R0P/SemD3Glue.lean | `1048576` 52 | `262144` 84 |
| R0P/SemDuplexDensity.lean | `Fin4` 124 | — |
| R0P/SemFiatShamir.lean | `Fin4` 63 | — |
| R0P/SemMaxErr.lean | `262144` 39,157; `9557` 39,157; `Fin4` 149 | `262144` 45,61,65,70; `9557` 45,61,65,69 |
| R0P/SemPad.lean | `1048576` 181,194 | `38230` 213 |
| R0Z/HonestView.lean | `Fin4` 35,62,201,206,305,413; `262144` 36,62,305,413; `256` 61,201,205,405; `childIndex` 202,203,206,220,336 | `childIndex` 416 |
| R0Z/PayloadSplit.lean | `256` 157; `262144` 166; `Fin4` 166 | — |
| R0Z/Z4Maps.lean | `262144` 34; `Fin4` 34 | — |
| Wide/Agreement.lean | `1048576` 47,52,168; `Fin4` 65,91,110; `262144` 66,111; `255` 93,114 | `9557` 119; `9558` 135; `38229` 176; `38230` 196 |
| Wide/ConcreteBranch.lean | `262144` 53; `Fin4` 52; `9557` 70; `1048576` 219; `38229` 236 | `262144` 88,119,165,172,177; `Fin4` 89; `9557` 132,169,181; `255` 85,152,161,165,166,181; `1048576` 255,287,344,351,357,376; `38229` 299,348,361 |
| Wide/DegreeThreeMatched.lean | `Fin4` 15,17,23,30,43,78 | — |
| Wide/EncoderLinearity.lean | `Fin4` 159,175,206; `256` 176 | — |
| Wide/FactorBudgets.lean | `1048576` 682,704,705,721,722; `initCap` 683; `262144` 693,713,714,727,728; `foldCap` 694; `38229` 706; `255` 714; `9557` 715 | `initCap` 685; `foldCap` 696 |
| Wide/FinalBranch.lean | `262144` 46,61; `Fin4` 45; `255` 58; `9557` 63 | `Fin4` 75 |
| Wide/FinalCurve.lean | `262144` 53,96,104,108; `Fin4` 52,95,105; `255` 56,103; `9557` 100 | `262144` 67,71; `Fin4` 68; `255` 66; `9557` 63 |
| Wide/FinalCurveBranch.lean | `262144` 49,68; `Fin4` 48; `9557` 53; `255` 65 | `262144` 82,91,94; `Fin4` 81; `9557` 87; `255` 95 |
| Wide/FinalEncoder.lean | `262144` 68,116,121; `255` 94 | `262144` 97,131,135,136,137; `255` 95; `256` 97,145; `slot` 131,132,134,139,141,145,149,174,175; `Fin4` 131,170; `childIndex` 132,134,135,136,137,141 |
| Wide/FinalRoot.lean | `262144` 69; `Fin4` 68; `255` 72 | `9557` 77 |
| Wide/FinalSelection.lean | `262144` 44; `Fin4` 43; `255` 47 | `262144` 58,74,102; `255` 57,71,101; `9557` 54 |
| Wide/GRSConversion.lean | `256` 29; `255` 29,73; `9558` 82,83; `1048576` 100,112,121,128,150,165; `38230` 221,222 | `256` 77 |
| Wide/Initial.lean | — | `1048576` 63; `38229` 50,55,57,80; `initCap` 51,64,66,81 |
| Wide/InitialBranch.lean | `1048576` 46,61; `38229` 63 | — |
| Wide/InitialCurve.lean | `1048576` 53,96,104,108; `38229` 100 | `1048576` 67,71; `38229` 63 |
| Wide/InitialCurveBranch.lean | `1048576` 49,68; `38229` 53 | `1048576` 82,91,94; `38229` 87 |
| Wide/InitialRoot.lean | `1048576` 100 | `38229` 108 |
| Wide/InitialSelection.lean | `1048576` 44 | `1048576` 58,74,102; `38229` 54 |
| Wide/Instances.lean | `initCap` 29; `foldCap` 30 | `38229` 17; `initCap` 17; `9557` 24; `foldCap` 24 |
| Wide/Interpolation.lean | `1048576` 587,588; `255` 595,599; `262144` 597,598 | — |
| Wide/JointList.lean | `38230` 30,84,97,131 | — |
| Wide/MatchedInstances.lean | `Fin4` 19,22,36,44; `262144` 20,37,45; `9557` 38,39,47,48; `foldCap` 39,48 | `9557` 40; `foldCap` 40 |
| Wide/MultiplicityThreeGS.lean | `1048576` 86,713,1249; `255` 73,74,76,77,688,798,826,1227; `262144` 74,1227; `9558` 75,858,881,894,911,951,1227; `38230` 87,1037,1058,1071,1088,1128,1249 | `1048576` 38,39,1141; `255` 48,49; `262144` 49,964; `9558` 692; `38230` 747 |
| Wide/Regression.lean | `38229` 19; `initCap` 19; `9557` 26; `foldCap` 26 | — |
| Wide/ReleasedLift.lean | `1048576` 212,215; `262144` 241,244; `Fin4` 250 | `Fin4` 264 |
| Wide/SubfieldDescent.lean | `1048576` 18,40,60,75 | — |
| Wide/Terminal.lean | `Fin4` 51,63,76,89 | `262144` 108,116; `9557` 104,109,112,133; `foldCap` 104,109,118,119,133; `255` 115 |
