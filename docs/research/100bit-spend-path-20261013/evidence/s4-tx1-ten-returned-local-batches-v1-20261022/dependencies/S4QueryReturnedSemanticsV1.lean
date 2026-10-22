import S4QueryTypedOpeningV1
import S4ClaimPowersSemanticV1
import S4ReturnedValueTransportV1
import S4FourSlotCurrentArraySemanticsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S4QueryReturnedSemanticsV1

open AspisR1.S4QueryTypedOpeningV1
open AspisR1.S4ClaimPowersSemanticV1
open AspisR1.S4ReturnedValueTransportV1
open AspisR1Stage2
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsV10CallbackOutputFieldResultsV1
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsV10CandidateQueryFieldEvidenceV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1S4P6PowersQueryJoinV1 (stage2ToClaim)
open AspisR1S4FourSlotCurrentArraySemanticsV1 (four_slot_values_are_first_fold_fibres)
open AspisR1FastDotsTailFieldProductRootV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)
open AspisR1.MixedLeafEncoding
open AspisR1.MixedLeafDecoder

abbrev CandidateQueryReturnedLocalBatchEvidence
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
    (powers : Array ClaimE 29#usize) (gamma : ClaimE) : Prop :=
  ∃ (i : U32) (u : Usize) (q : Slice U8)
    (candidateValues : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 4#usize)
    (currentValues : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 4#usize)
    (arrayQ : Array U8 608#usize)
    (v0 v1 v2 v3 : AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact)
    (c1 : C1) (c2 : C2),
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
    arrayQ.val.map AspisR1.ExtractedRecordByteValue.rawByte =
      encodeC1 c1 ++ encodeC2 c2 ∧
    candidateValues.val.map
      (fun x => AspisR1CurrentPreparedClaim.Concrete.decode
        (stage2ToClaim x)) =
      List.ofFn (fun slot : Fin 4 =>
        AspisV6Width29CorrelatedAgreement.width29Batch
          (AspisR1D18S4ConcreteWidth29KernelV1.localWord c1 c2 slot)
          (AspisR1CurrentPreparedClaim.Concrete.decode gamma))

/-- The same successful ClaimPowers call supplies the coefficient meaning for
the same four callback witnesses.  The returned Full array is decoded via the
same returned Current array, while the typed opening and callback identities
are retained in the result witness. -/
theorem typed_opening_returned_local_batches
    (rest : QueryOps) (proof : Slice U8) (p : verifier.Prepared)
    (a : verifier.Accumulator)
    (g : Array AspisR1Stage2.aspis_core.field.wide_exact.WideExact 29#usize)
    (powers : Array ClaimE 29#usize) (gamma : ClaimE)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma =
      .ok powers)
    (he : CandidateQueryTypedOpeningEvidence rest proof p a g powers) :
    CandidateQueryReturnedLocalBatchEvidence rest proof p a g powers gamma := by
  rcases he with ⟨i,u,q,candidateValues,currentValues,arrayQ,v0,v1,v2,v3,c1,c2,
    hi,hu,hopening,hread,hdots,hcurrent,ha,hcanonical,hlist,hf0,hf1,hf2,hf3,
    hc1,hc2,hbytes⟩
  let gammaWide := AspisR1CurrentPreparedClaim.Concrete.decode gamma
  have hpowersWide := successful_powers_exact gamma powers hgamma hpowers
  have hlocal := four_slot_values_are_first_fold_fibres
    arrayQ (claimArrayToFast powers) currentValues v0 v1 v2 v3 hlist
    gammaWide c1 c2 hbytes hpowersWide hf0 hf1 hf2 hf3
  have htransport := same_returned_array_decode currentValues candidateValues hcurrent
  exact ⟨i,u,q,candidateValues,currentValues,arrayQ,v0,v1,v2,v3,c1,c2,
    hi,hu,hopening,hread,hdots,hcurrent,ha,hcanonical,hlist,hf0,hf1,hf2,hf3,
    hc1,hc2,hbytes, by
      simpa [gammaWide] using htransport.trans hlocal⟩

#print axioms typed_opening_returned_local_batches
end AspisR1S4QueryReturnedSemanticsV1
