# PCUD_ HANDOFF: phase P2d (c1/c2 field/sampler/parser/caller-model modules + P5 queue)

Target not yet established. No ledger row, trust row, RSL, security contract or shipped source changed.

Branch codex/pc-prov-p2d-20261109 (base research 045798ab94b). Host workspace /home/dombarker/project-offloads/codex-pc-prov-p2d-20261109/. Frozen source 4bb3b3f5.

## Claims (exact)
82 modules, 569 reached definitions (PCUD_EQ_STATUS.json totals): {"NO_COMMON_LEAN_NAME": 88, "NO_FRESH_EMISSION": 231, "PROVED_RFL": 63, "PROVED_UNFOLD": 71, "FAILED": 64, "CONFIG_PENDING_OVERFLOW_CHECKS": 52}.
PROVED_RFL / PROVED_UNFOLD: theorem `PRVEq.<M><tag>.<name> : @PRVFresh_.. = @<gate>.<name>` compiled in the verify scopes listed in `verify_bundles` (L002, L011, L012, L013, L015, L016, L019, all exit 0), `#print axioms` only propext/Classical.choice/Quot.sound (all 134 checked, axioms_ok true), no sorry/native_decide, maxHeartbeats only as in the Aeneas header. Statements are against compiled gate constants. The comparison is against frozen-pinned retained or raw emissions chosen by Rust-symbol presence; the compiled-source self-copy control was not run (PCUD-C8).
CONFIG_PENDING_OVERFLOW_CHECKS (52): checked-vs-wrapping body differences and callers blocked by them; not SEMANTIC, not P3; await overflow-checks-on emissions (P1a/P1b redo). One non-overflow FAILED(semantic-class) remains: R1CandidateWideParserSource WideExact.from_le_bytes (slice-index form differs).
FAILED (64, 63 transport-needed: fresh declarations or callees do not elaborate against the gate environment): data for P3. NO_COMMON_LEAN_NAME 88. NO_FRESH_EMISSION 231 (P1a pending / P1 failure lists).

## Scopes
19 Lean scopes of 40, 0 extraction scopes, strictly one at a time, caps 6G/8G swap 0 tasks 64, 180 s, unraised. Kills: L003, L006, L014 (exit 134, memory_exception); L017 failed verify (generator bug, PCUD-C4). Receipts: PCUD_L0nn/receipt.json, PCUD_ATTEMPTS.jsonl. Peak RSS up to 7.4 GB (L014).

## Per module counts
- AspisC2HostEmbedding.Funs: {'NO_COMMON_LEAN_NAME': 4}
- AspisC2HostEmbedding.Types: {'NO_COMMON_LEAN_NAME': 5}
- AspisR1BatchedWeightsExtraction.Types: {'NO_FRESH_EMISSION': 4}
- AspisR1CanonicalDotFinish.Funs: {'NO_FRESH_EMISSION': 4}
- AspisR1CanonicalDotFinish.Types: {'NO_FRESH_EMISSION': 1}
- AspisR1CircleFallback.Types: {'PROVED_RFL': 4, 'NO_COMMON_LEAN_NAME': 1}
- AspisR1CircleSampleWrapper.Types: {'PROVED_RFL': 4, 'NO_COMMON_LEAN_NAME': 1, 'NO_FRESH_EMISSION': 1}
- AspisR1DecodeKFullV10.Funs: {'NO_FRESH_EMISSION': 5}
- AspisR1DecodeKFullV10.Types: {'PROVED_RFL': 4, 'NO_COMMON_LEAN_NAME': 1}
- AspisR1DotPushLocal.Funs: {'NO_FRESH_EMISSION': 2}
- AspisR1DotPushLocal.Types: {'NO_FRESH_EMISSION': 2}
- AspisR1EbyKFinish.Funs: {'PROVED_UNFOLD': 2, 'NO_FRESH_EMISSION': 5}
- AspisR1EbyKFinish.Types: {'PROVED_RFL': 4, 'NO_FRESH_EMISSION': 3}
- AspisR1GammaCaller.Types: {'PROVED_RFL': 3, 'NO_FRESH_EMISSION': 1}
- AspisR1Post25Sampler.Funs: {'FAILED': 6, 'NO_COMMON_LEAN_NAME': 6, 'NO_FRESH_EMISSION': 3}
- AspisR1Post25Sampler.Types: {'PROVED_RFL': 3, 'NO_FRESH_EMISSION': 2}
- AspisR1Post25SamplerIndexedAddSmallCandidate.Funs: {'FAILED': 3, 'PROVED_UNFOLD': 1}
- AspisR1PrefixAggregateParser.Funs: {'PROVED_UNFOLD': 11, 'FAILED': 1, 'PROVED_RFL': 2, 'NO_FRESH_EMISSION': 5}
- AspisR1Qm31SamplerIndex.Funs: {'FAILED': 7, 'PROVED_RFL': 2, 'NO_COMMON_LEAN_NAME': 2}
- AspisR1QueryGeometryActual.Funs: {'PROVED_RFL': 1, 'PROVED_UNFOLD': 2, 'FAILED': 2}
- AspisR1SemanticCallExtraction.Funs: {'PROVED_UNFOLD': 3, 'FAILED': 1, 'NO_FRESH_EMISSION': 16, 'NO_COMMON_LEAN_NAME': 2}
- AspisR1SemanticCallExtraction.Types: {'NO_FRESH_EMISSION': 3}
- AspisR1WideToBytesIndexedCandidate.FunsNoResourceOptions: {'PROVED_RFL': 1, 'FAILED': 1}
- AspisR1WideToBytesSource.Funs: {'PROVED_RFL': 1, 'FAILED': 3}
- AspisR1WithdrawalCaller.Funs: {'PROVED_UNFOLD': 1, 'NO_FRESH_EMISSION': 20}
- AspisR1WithdrawalCaller.Types: {'PROVED_RFL': 1, 'NO_FRESH_EMISSION': 2, 'NO_COMMON_LEAN_NAME': 2}
- AspisR72Sampler.Funs: {'PROVED_UNFOLD': 5, 'CONFIG_PENDING_OVERFLOW_CHECKS': 22, 'PROVED_RFL': 5, 'NO_FRESH_EMISSION': 7, 'NO_COMMON_LEAN_NAME': 1}
- AspisR72Sampler.Types: {'PROVED_RFL': 4, 'NO_COMMON_LEAN_NAME': 1, 'NO_FRESH_EMISSION': 1}
- AspisV8R19.ComplexFieldSlice: {'PROVED_UNFOLD': 1, 'CONFIG_PENDING_OVERFLOW_CHECKS': 8, 'NO_COMMON_LEAN_NAME': 1}
- AspisV8R19.GuardedFieldSlice: {'PROVED_UNFOLD': 1, 'CONFIG_PENDING_OVERFLOW_CHECKS': 6}
- AspisV8R19.QuarticFieldSlice: {'PROVED_UNFOLD': 1, 'CONFIG_PENDING_OVERFLOW_CHECKS': 10, 'PROVED_RFL': 1, 'NO_COMMON_LEAN_NAME': 1, 'NO_FRESH_EMISSION': 1}
- ClaimsUnrolledParentSource: {'NO_FRESH_EMISSION': 2}
- ClaimsUnrolledParentTypes: {'NO_FRESH_EMISSION': 7}
- CurrentClaimDotModel: {'NO_FRESH_EMISSION': 6}
- CurrentClaimSumModel: {'NO_FRESH_EMISSION': 15}
- CurrentCompactCallerModelV1: {'FAILED': 8, 'PROVED_UNFOLD': 2, 'PROVED_RFL': 1}
- CurrentCompactCallerTypesV1: {'PROVED_RFL': 3, 'NO_COMMON_LEAN_NAME': 15}
- CurrentPowersCallback: {'NO_COMMON_LEAN_NAME': 3, 'NO_FRESH_EMISSION': 1}
- EbyKPushExplicitTypesV1: {'PROVED_RFL': 1, 'NO_COMMON_LEAN_NAME': 6, 'NO_FRESH_EMISSION': 1}
- FIn_WeightsTypes: {'NO_COMMON_LEAN_NAME': 4, 'NO_FRESH_EMISSION': 1}
- FinishCandidateExplicitOps: {'PROVED_RFL': 2, 'FAILED': 4}
- GammaCallerExplicitHelpers: {'FAILED': 1}
- Hiq_DispatchSource: {'NO_FRESH_EMISSION': 1}
- LoopPowersCandidateModel: {'PROVED_UNFOLD': 2, 'NO_COMMON_LEAN_NAME': 3, 'NO_FRESH_EMISSION': 2}
- LoopPowersEarlySteps: {'NO_COMMON_LEAN_NAME': 2}
- NFG_CheckedFieldRef.Funs: {'PROVED_UNFOLD': 1, 'CONFIG_PENDING_OVERFLOW_CHECKS': 2, 'NO_FRESH_EMISSION': 1}
- NFN_ExtractedGeometry: {'NO_FRESH_EMISSION': 25}
- NGN_Emitted: {'NO_COMMON_LEAN_NAME': 3}
- NGT_Emitted: {'NO_COMMON_LEAN_NAME': 4}
- NID_ResumeEmissionFuns: {'PROVED_RFL': 1, 'FAILED': 1}
- NJA_CountBody: {'PROVED_RFL': 5, 'FAILED': 1, 'NO_COMMON_LEAN_NAME': 1}
- NJA_Multiproof.Types: {'PROVED_RFL': 2, 'NO_COMMON_LEAN_NAME': 1}
- NJC_ReaderEmission: {'FAILED': 2, 'NO_COMMON_LEAN_NAME': 1}
- NJT_ClaimsRef_Funs: {'NO_FRESH_EMISSION': 1}
- NMT_first.Funs: {'PROVED_RFL': 2, 'FAILED': 2}
- NMT_stage1_owned.Funs: {'FAILED': 2}
- NMT_tx1.Funs: {'PROVED_UNFOLD': 13, 'FAILED': 1}
- R1CandidateFieldParsers: {'PROVED_UNFOLD': 4, 'NO_COMMON_LEAN_NAME': 3}
- R1CandidateWideParserSource: {'PROVED_UNFOLD': 1, 'FAILED': 1, 'NO_COMMON_LEAN_NAME': 1}
- RPz7_AspisR1CircleSampleWrapper_Funs: {'FAILED': 1}
- RPz7_WAdm_Fissioned_Funs: {'NO_FRESH_EMISSION': 24}
- S1ClaimBorrowedAbiNativeV1: {'NO_FRESH_EMISSION': 11}
- S1ClaimBoundedResultCompositionV1: {'NO_FRESH_EMISSION': 1}
- S1ClaimOwnedNestedModelV1: {'NO_FRESH_EMISSION': 10}
- S1NativeCompactModelV1: {'PROVED_UNFOLD': 5, 'FAILED': 6, 'PROVED_RFL': 1}
- S1ValuesOwnedModelV1: {'NO_FRESH_EMISSION': 8}
- S2StdAnySourceV1: {'NO_FRESH_EMISSION': 3}
- S8OwnedP6.Funs: {'NO_COMMON_LEAN_NAME': 1, 'NO_FRESH_EMISSION': 8}
- S8OwnedP6.Types: {'PROVED_RFL': 3, 'NO_FRESH_EMISSION': 1}
- SelectedWideViewFunsV1: {'PROVED_UNFOLD': 15, 'NO_FRESH_EMISSION': 1}
- SelectedWideViewTypesV1: {'PROVED_RFL': 1, 'NO_COMMON_LEAN_NAME': 5}
- UnrolledWideParserSource: {'NO_COMMON_LEAN_NAME': 2}
- WeightsFieldExplicitDecoder: {'FAILED': 1}
- AspisR1WithdrawalValidation.Types: {'PROVED_RFL': 1, 'NO_COMMON_LEAN_NAME': 1, 'NO_FRESH_EMISSION': 1}
- S8Kani2MutableSource: {'NO_FRESH_EMISSION': 9}
- VTop_Model: {'FAILED': 3}
- Port3_NativeBatchBody: {'CONFIG_PENDING_OVERFLOW_CHECKS': 2, 'FAILED': 3}
- Port3_NativeGeometryBody: {'FAILED': 3, 'CONFIG_PENDING_OVERFLOW_CHECKS': 2}
- Port5Q2_ReaderWeights: {'NO_COMMON_LEAN_NAME': 2}
- Port5Q2_ReaderValidate: {'NO_COMMON_LEAN_NAME': 2}
- Op4P_Extract.Types: {'NO_FRESH_EMISSION': 1}
- NDH_Reference.Funs: {'NO_FRESH_EMISSION': 2}

## Files
PRVEq_*.lean (final per label), PCUD_EQ_STATUS.json, PCUD_FOR_P3.json, PCUD_HAND_MODELS.json, PCUD_CLASSIFICATIONS.json, PCUD_TOOLS.json, gen/ (states, reports, probe logs, round copies), inputs/ (fresh and gate sources used).

## Remaining
Overflow-checks-on re-comparison of the pending definitions; P1a emissions for the 231 NO_FRESH_EMISSION; compiled-source controls; the 63 transport-needed and 88 name-mismatch items (P3); the P5 queue items for AdapterRwModel/FIn_WeightsFuns/RecordParser/QueryGeometry Types belong to the hub clusters or P3 and were not re-run here.
