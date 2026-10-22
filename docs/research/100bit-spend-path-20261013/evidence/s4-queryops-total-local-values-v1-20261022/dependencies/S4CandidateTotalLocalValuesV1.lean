import S4ConcreteV10CandidateEndpointV1
import S4ScannedOpeningDecodeV1
import S4ClaimPowersSemanticV1
import S4FourSlotCurrentArraySemanticsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S4CandidateTotalLocalValuesV1
open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsV10LiteralOuterTransferRootV1 (literalV10Outer)
open AspisR1FastDotsV10TypedInnerBodyOpsV1 (mapWideArray)
open AspisR1FastDotsV10CarrierMapV1 (V10Wide)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
open AspisR1S4FourWrapperCarrierTransportRootV1 (mapArray)
open AspisR1.MixedLeafEncoding AspisR1.MixedLeafDecoder

/-- The complete candidate entry succeeds and its four actual outputs are the
width29 batches of the very same strictly decoded opening. No successful
entry/helper/callback result or independent decoded opening is assumed. -/
theorem candidate_entry_total_exact_batches
    (proof : Slice U8) (j : Nat) (q : Slice U8)
    (input : Array V10Wide 29#usize)
    (gamma : ClaimE) (powers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok powers)
    (hcaller : mapWideArray input = claimArrayToFast powers)
    (hlen : proof.val.length = 57607) (hj : j < 22)
    (hread : q.val = proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    ∃ literalValues currentValues, ∃ (a : Array U8 608#usize) (c1 : C1) (c2 : C2),
      literalV10Outer concreteOps q input = .ok literalValues ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots_fixed concreteOps q
        (mapWideArray input) = .ok currentValues ∧
      mapArray AspisR1FastDotsV10CarrierMapV1.wideToEbyK literalValues = currentValues ∧
      a.val = q.val.slice 0 (608#usize) ∧
      (∀ x ∈ currentValues.val, AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      decodeC1 ((a.val.map AspisR1.ExtractedRecordByteValue.rawByte).take 480) = some c1 ∧
      decodeC2 ((a.val.map AspisR1.ExtractedRecordByteValue.rawByte).drop 480) = some c2 ∧
      currentValues.val.map (fun x => AspisR1CurrentWide.Proof.decodeWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) =
        List.ofFn (fun slot : Fin 4 => AspisV6Width29CorrelatedAgreement.width29Batch
          (AspisR1D18S4ConcreteWidth29KernelV1.localWord c1 c2 slot)
          (AspisR1CurrentPreparedClaim.Concrete.decode gamma)) := by
  obtain ⟨lv,cv,a,v0,v1,v2,v3,hl,hc,hm,ha,hcanon,hlist,hf0,hf1,hf2,hf3⟩ :=
    AspisR1FastDotsConcreteV10CandidateEndpointV1.concrete_literal_outer_total_and_field_results_from_scan
      proof j q input gamma powers hgamma hpowers hcaller hlen hj hread hscan
  obtain ⟨c1,c2,hd1,hd2,hbytes⟩ :=
    AspisR1.S4ScannedOpeningDecodeV1.scanned_opening_decode proof j q a hlen hj hread hscan ha
  have hexact := AspisR1.S4ClaimPowersSemanticV1.successful_powers_exact
    gamma powers hgamma hpowers
  rw [hcaller] at hf0 hf1 hf2 hf3
  have hvalues := AspisR1S4FourSlotCurrentArraySemanticsV1.four_slot_values_are_first_fold_fibres
    a (claimArrayToFast powers) cv v0 v1 v2 v3 hlist
    (AspisR1CurrentPreparedClaim.Concrete.decode gamma) c1 c2 hbytes hexact hf0 hf1 hf2 hf3
  exact ⟨lv,cv,a,c1,c2,hl,hc,hm,ha,hcanon,hd1,hd2,hvalues⟩

#print axioms candidate_entry_total_exact_batches
end AspisR1.S4CandidateTotalLocalValuesV1
