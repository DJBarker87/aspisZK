import S4QueryReturnedSemanticsV1
import S4CurrentArrayModelInputsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4QueryReturnedModelV1

open AspisR1Stage2
open AspisR1
open AspisR1.S4QueryTypedOpeningV1
open AspisR1S4QueryReturnedSemanticsV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsV10CandidateQueryFieldEvidenceV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1S4P6PowersQueryJoinV1 (stage2ToClaim)
open AspisR1FastDotsTailFieldProductRootV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)
open AspisR1.MixedLeafEncoding
open AspisR1.MixedLeafDecoder
open AspisR1.ExactBaseProjection
open AspisR1.ExactLeafFieldCodec
open AspisV8R19.DuplexFrames

abbrev CandidateQueryReturnedModelEvidence
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
    (powers : Array AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE 29#usize)
    (gamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE) : Prop :=
  ∃ (i : U32) (u : Usize) (q : Slice U8)
    (candidateValues : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 4#usize)
    (currentValues : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 4#usize)
    (arrayQ : Array U8 608#usize)
    (v0 v1 v2 v3 : AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact)
    (c1 : AspisR1.MixedLeafEncoding.C1)
    (c2 : AspisR1.MixedLeafEncoding.C2),
    Array.index_usize p.queries a.next = .ok i ∧
    lift (UScalar.cast .Usize i) = .ok u ∧
    sourceOpening proof a.next = .ok q ∧
    q.val = proof.val.slice (10055 + a.next.val * 832)
      (10055 + a.next.val * 832 + 832) ∧
    (concreteCandidateQueryOps rest).dots q g = .ok candidateValues ∧
    currentArrayToFull currentValues = candidateValues ∧
    arrayQ.val = q.val.slice 0 (608#usize) ∧
    (∀ x ∈ currentValues.val,
      AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
    currentValues.val = [v0,v1,v2,v3] ∧
    LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
      arrayQ (claimArrayToFast powers) 0#usize v0 ∧
    LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
      arrayQ (claimArrayToFast powers) 1#usize v1 ∧
    LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
      arrayQ (claimArrayToFast powers) 2#usize v2 ∧
    LiteralFieldResult
      (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
      arrayQ (claimArrayToFast powers) 3#usize v3 ∧
    decodeC1 ((arrayQ.val.map AspisR1.ExtractedRecordByteValue.rawByte).take 480) = some c1 ∧
    decodeC2 ((arrayQ.val.map AspisR1.ExtractedRecordByteValue.rawByte).drop 480) = some c2 ∧
    arrayQ.val.map AspisR1.ExtractedRecordByteValue.rawByte = encodeC1 c1 ++ encodeC2 c2 ∧
    candidateValues.val.map
      (fun x => AspisR1CurrentPreparedClaim.Concrete.decode
        (stage2ToClaim x)) =
      List.ofFn (fun slot : Fin 4 =>
        AspisV6Width29CorrelatedAgreement.width29Batch
          (AspisR1D18S4ConcreteWidth29KernelV1.localWord c1 c2 slot)
          (AspisR1CurrentPreparedClaim.Concrete.decode gamma)) ∧
    ∀ (packed1 packed2 : Fin 262144 → Option AspisV8R19.DuplexFrames.Bytes)
      (leaf : Fin 262144),
      packed1 leaf = some ((arrayQ.val.map AspisR1.ExtractedRecordByteValue.rawByte).take 480) →
      packed2 leaf = some ((arrayQ.val.map AspisR1.ExtractedRecordByteValue.rawByte).drop 480) →
      candidateValues.val.map
        (fun x => AspisR1CurrentPreparedClaim.Concrete.decode
          (stage2ToClaim x)) =
      List.ofFn (fun slot : Fin 4 => FirstFold.fibre
        (TwoFoldExtraction.batchedWord
          (TypedRecoveredWords.word ExactBaseProjection.embed
            (algebraMap QM31Exact AspisR1FastDotsTailFieldProductRootV1.TowerWide)
            packed1 packed2)
          (AspisR1CurrentPreparedClaim.Concrete.decode gamma)) leaf slot)

/-- Transport the same four callback results to the recovered-word first-fold
model when the caller supplies packed maps for the exact opening bytes. The map
condition is inside the original query witness, so it cannot select a different
query or a different 608-byte prefix. This does not assert that `leaf` is the
source cast index `u` from the query geometry; that caller-level alignment is
upstream. -/
theorem returned_local_batches_model_transport
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
    (powers : Array AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE 29#usize)
    (gamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE)
    (hret : CandidateQueryReturnedLocalBatchEvidence rest proof p a g powers gamma) :
    CandidateQueryReturnedModelEvidence rest proof p a g powers gamma := by
  rcases hret with ⟨i,u,q,candidateValues,currentValues,arrayQ,v0,v1,v2,v3,c1,c2,
    hi,hu,hopening,hread,hdots,hcurrent,ha,hcanonical,hlist,hf0,hf1,hf2,hf3,
    hc1,hc2,hbytes,hlocal⟩
  refine ⟨i,u,q,candidateValues,currentValues,arrayQ,v0,v1,v2,v3,c1,c2,
    hi,hu,hopening,hread,hdots,hcurrent,ha,hcanonical,hlist,hf0,hf1,hf2,hf3,
    hc1,hc2,hbytes,hlocal,?_⟩
  intro packed1 packed2 leaf hp1 hp2
  have hmodel := AspisR1.S4LocalBatchModelTransportV1.four_slot_local_batches_are_model_inputs
    AspisR1.ExactBaseProjection.embed
    (algebraMap AspisR1.ExactLeafFieldCodec.QM31Exact
      AspisR1FastDotsTailFieldProductRootV1.TowerWide)
    packed1 packed2 leaf
    (arrayQ.val.map AspisR1.ExtractedRecordByteValue.rawByte) c1 c2
    (AspisR1CurrentPreparedClaim.Concrete.decode gamma)
    hp1 hp2 hc1 hc2
  exact hlocal.trans hmodel

#print axioms returned_local_batches_model_transport
end AspisR1S4QueryReturnedModelV1
