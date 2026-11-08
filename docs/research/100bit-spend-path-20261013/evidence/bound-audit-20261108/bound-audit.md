# Bound audit: total(Q), maxQueries, E_rec (read-only, research @ 0f96d517e6a)

Script: bound_audit.py (exact Fraction/int; Decimal only to print logs). Output: bound_audit_output.txt. 31/31 checks PASS.

## Headline conjuncts (kernel print, evidence/batch-merkle5-20261110/NLL_L072/stdout.log l.1130-1170; same text as evidence/replay-deployed2-20261027/RPx_Deployed.lean)
- `F3T_RuntimeBound.failureModel runtime ≤ F3T_Numeric.total (Q0+Q1)`
- `Q0+Q1 ≤ F3U_RangeEdges.maxQueries → failureModel runtime ≤ (Q0+Q1+1)·(1/2^100)`
- `Q0+Q1 = 0 → F3U_Numeric.margin ≤ 1/2^100 − failureModel runtime ∧ failureModel runtime < 1/2^100`
- separately: `F3Y_AccountMass.Claims … (Q0+Q1) select` (E_head mass ≤ accountLoss; constant selector), and conjunct 4 `FJv_DResult.Outcome … (event iv (Q0+Q1+2965) …E_head…)`.

`failureModel runtime := deployedFailure runtime + QueryScanModelFailure.failureProbability (2^18)` (lean/F3T_RuntimeBound.lean).
Proof: `FJp_Residual.numeric` = `FJp_Mass.bounded` (deployedFailure ≤ modelMean + accountLoss) + `F3T_ModelClaims.failure_bound` (modelMean + scan ≤ StartChargeNumeric.totalBound) + `le_refl accountLoss`, closed by `F3T_Combined.arithmetic` (totalBound + accountLoss = total).

## Term-by-term trace
| term | Lean definition | event / loss charged | Lean origin |
|---|---|---|---|
| (Q+34)·B, B = 15/2^109 | `PerAttemptEnvelope.B : ℚ := 15 / 2^109`; `envelope Q 34 1161` | classifier hit among Q adversary queries + 34 transcript starts read in the prover/sampler prefix | `F3T_Probability.restricted_union_bound` |
| 6(Q+1161)²/2^256 | `F3T_Numeric.collisionLoss` = `BinCombinedMerkleCollision.kappa (Q+1161)` = 6Q²/256^32 | `RecordedBinaryExperimentBin.binaryCollision (Q+1161)`; Q+1161 distinct first reads of the canonical model run | `F3T_Accounting.first_reads`, `F3T_Probability.failure_bound` |
| 6(Q+2965)²/2^256 | `F3T_Numeric.accountLoss` | E_rec: `BinRawByteCollisionTargets.event iv (Q0+Q1+2965)` on `Hiq_RecordedJoint.program (ARX_LocalCharge.bounded (ART_PartialAccount.account cfg …a) (Q0+Q1)) ARQ_Observer.project (ARQ_Observer.select …)`; first reads ≤ Q+1921, +1044 recorder reads | `FJp_Mass.bounded`, `F3T_AccountCharge.bound`, `Hiq_RecordedBudget.queries` (+1044) |
| 2^-126 | literal in `envelope` | extractor random-coin abort: accepted, no hit, extractor still returns none (`bankAbortMass_le`) | `RawRecordedOracleExtractionMassBin.shared_oracle_failure_le_hit_add_abort` |
| 2^-454 | literal in `envelope`; `failureProbability (2^18)` | Q22 64-draw query-scan exhaustion (fails to collect 22 distinct positions) | `QueryScanModelFailure.exhaustion_bound` |

Contract: 2026-10-21 table (34·B + κ(1161) + 2^-126 + 2^-454) plus frozen3 amendment 2026-10-26 (margin with 6(1161²+2965²)); 2026-10-27 ARX amendment names `F3T_Numeric.total Q` and the event at Q+2965; 2026-10-27 (second) item 2 fixes `maxQueries`. All agree with the Lean.

## (1) Inequality and range — exact
- `total(Q) − (Q+1)/2^100 = F3U_RangePolynomial.gap(Q)` and `startcharge + accountLoss = total` checked at 9 points incl. maxQ, maxQ+1, 2^160 (quadratics; ≥3 points suffice).
- gap·2^454 = A Q² + B Q + C with A = 12·2^198 > 0 and C < 0, so {Q ≥ 0 : gap ≤ 0} = [0, r]. Integer root via isqrt: r = 7388980242446479800895501321004157112314840375 = `F3U_RangeEdges.maxQueries` exactly; total(maxQ) ≤ (maxQ+1)/2^100 and total(maxQ+1) > (maxQ+2)/2^100. log2 maxQ = 152.37214. `F3U_RangeMaximal.exact_range` (iff) is consistent.
## (2) E_rec / accountLoss
- accountLoss appears exactly once in `total`; inserted once (`FJp_Residual.numeric`, `le_refl accountLoss`). E_head's mass bound (`F3Y_AccountMass.Claims`) is a separate conjunct, never added: no double count.
- Not missing from failureModel. But no compiled theorem bounds the combined event "extractor fails OR Outcome fails": conjunct 4 is per-world. The single-charge statement `mean max r 1_{¬OutcomeRec} ≤ total(Q)` rests on `RSL.EVB.no_second_charge` (abstract pointwise ℚ fact, stand-in) plus an uncompiled averaging step and host theorem (draft §1.2.2 says so). Option A (second accountLoss) range 4925986828297653200597000880669438074876558273 (2^151.787) reproduced; ratio to maxQ is 0.666…6664, not exactly 2/3 as EVB says (immaterial).
## (3) Q = 0
total(0) = 0.99609376490116·2^-100 = 2^-100.0056465. Headroom 0.0056 bits. Margin 2^-100 − total(0) = 0.9999961853·2^-108 = 2^-108.0000055; equals `F3U_Numeric.margin` exactly. Start charge is 99.9999985% of total(0); accountLoss(0) ≈ 5.8e-40 of it, so the margin is insensitive to E_rec counting.
## (4) Per-attempt / metric
(A) whole experiment with zero adversary queries: total(0) < 2^-100, in the headline. (B) explicit total(Q) for every Q (conjunct 1, no range). Q counts every adversary-issued digest call across both phases (`ARW_Induced.issued`; verifier-internal calls are not in Q but in the 34/1161/2965 envelopes), so Q = 0 is attainable (constant adversary). No division by work, no PoW/grinding term anywhere in `total`. (Q+1)·2^-100 is labelled a corollary, not a per-query rate. Multi-submission campaigns: no Lean theorem; the draft's §3.5 reduction is informal (draft says so). Q is counted on a⊤ under option B (draft §7.3).
## (5) Discrepancies draft vs Lean
1. §3.2(B) "(Q+1)·2^-100 looser than total(Q) by about 2^4.9": wrong for most of the range; it is 2^5.093 (= log2(512/15)) for Q ≳ 10^4; 2^4.9 only near Q ≈ 233.
2. §3.1 table cites "contract 2026-10-21" for 2^-126 and 2^-454; the Lean sources are `shared_oracle_failure_le_hit_add_abort`/`bankAbortMass_le` and `QueryScanModelFailure.exhaustion_bound`. Citation only.
3. §1.1 "at every H … failureModel ≤ total(Q)": failureModel is an average over H; C5num is H-free. Wording.
4. "E_rec charged once" holds in compiled Lean only for failureModel; for the per-attempt event including OutcomeRec it is stand-in + uncompiled host statement (acknowledged in §1.2.2 but §1.1 and §3.1 state it as fact).
5. `F3T_Numeric.accountLoss` docstring still says source-event transport is not established; `FJp_Mass.bounded` now establishes it. Stale comment, Lean side.
No numeric error: every constant, the inequality, maxQueries and the Q = 0 margin are exactly right.
