import S4CandidateTotalLocalValuesV1
import S4V10ConcreteQueryOpsBuilderV1
import S4ReturnedValueTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4QueryOpsTotalLocalValuesV1
open AspisR1Stage2
open AspisR1FastDotsV10ConcreteQueryOpsBuilderV1
open AspisR1FastDotsV10QueryOpsResultTransportV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1S4FullQueryValuesPrefixV1
open AspisR1FastDotsV10TypedInnerBodyOpsV1 (mapWideArray)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1.MixedLeafEncoding AspisR1.MixedLeafDecoder

/-- Forward totality and exact values for the dots slot installed in actual
candidate query operations. No successful dots invocation is a premise. -/
theorem candidate_queryops_dots_total_exact_batches
    (rest : QueryOps) (proof : Slice U8) (j : Nat) (q : Slice U8)
    (g : Array FullWide 29#usize) (gamma : ClaimE) (powers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers)
    (hcaller : fullArrayToCurrent g = claimArrayToFast powers)
    (hlen : proof.val.length = 57607) (hj : j < 22)
    (hread : q.val = proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    ∃ values, ∃ (a : Array U8 608#usize) (c1 : C1) (c2 : C2),
      (concreteCandidateQueryOps rest).dots q g = .ok values ∧
      a.val = q.val.slice 0 (608#usize) ∧
      decodeC1 ((a.val.map AspisR1.ExtractedRecordByteValue.rawByte).take 480) = some c1 ∧
      decodeC2 ((a.val.map AspisR1.ExtractedRecordByteValue.rawByte).drop 480) = some c2 ∧
      values.val.map (fun x => AspisR1CurrentPreparedClaim.Concrete.decode
        (AspisR1S4P6PowersQueryJoinV1.stage2ToClaim x)) =
        List.ofFn (fun slot : Fin 4 => AspisV6Width29CorrelatedAgreement.width29Batch
          (AspisR1D18S4ConcreteWidth29KernelV1.localWord c1 c2 slot)
          (AspisR1CurrentPreparedClaim.Concrete.decode gamma)) := by
  have hmap : mapWideArray (fullArrayToV10 g) = claimArrayToFast powers := by
    rw [fullArrayToV10_map]
    exact hcaller
  obtain ⟨lv,cv,a,c1,c2,hl,hc,hm,ha,hcanon,hd1,hd2,hvalues⟩ :=
    AspisR1.S4CandidateTotalLocalValuesV1.candidate_entry_total_exact_batches
      proof j q (fullArrayToV10 g) gamma powers hgamma hpowers hmap hlen hj hread hscan
  have hdots : (concreteCandidateQueryOps rest).dots q g =
      .ok (currentArrayToFull cv) := by
    change literalDots concreteOps q g = _
    rw [concrete_candidate_dots_is_literal_v10 q g]
    simp only [hl, bind_tc_ok, hm]
  have hdecode := AspisR1.S4ReturnedValueTransportV1.same_returned_array_decode
    cv (currentArrayToFull cv) rfl
  exact ⟨currentArrayToFull cv,a,c1,c2,hdots,ha,hd1,hd2,hdecode.trans hvalues⟩

#print axioms candidate_queryops_dots_total_exact_batches
end AspisR1.S4QueryOpsTotalLocalValuesV1
