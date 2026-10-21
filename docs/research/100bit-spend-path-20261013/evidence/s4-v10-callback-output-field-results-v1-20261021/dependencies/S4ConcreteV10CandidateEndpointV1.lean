import S4ConcreteKernelOpsRootV1
import S4V10LiteralScannedTotalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsConcreteV10CandidateEndpointV1

open AspisR1FastDotsConcreteKernelOpsRootV1 (concreteOps)
open AspisR1FastDotsV10LiteralScannedTotalV1
  (literal_outer_total_and_field_results_from_scan)
open AspisR1FastDotsV10LiteralOuterTransferRootV1 (literalV10Outer)
open AspisR1S4FourWrapperCarrierTransportRootV1 (mapArray)
open AspisR1FastDotsV10TypedInnerBodyOpsV1 (mapWideArray)
open AspisR1FastDotsV10CarrierMapV1 (V10Wide)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
  (ClaimE ClaimCanonical claimArrayToFast)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)

/-- Scanner-derived totality for the complete, source-body-checked V10 literal
four-call outer cut, with the selected eleven operation slots fixed to the
accepted concrete implementation. The candidate's exact Rust `fast_dots.rs`
source hash and generated-body identity are checked by the adjacent V10
extraction/source packets. The caller's V10-to-current array identity remains
an explicit premise for the upstream caller bridge. -/
theorem concrete_literal_outer_total_and_field_results_from_scan
    (proof : Slice Std.U8) (j : Nat) (q : Slice Std.U8)
    (input : Array V10Wide 29#usize)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : mapWideArray input = claimArrayToFast claimPowers)
    (hlen : proof.val.length = 57607) (hj : j < 22)
    (hread : q.val = proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    ∃ (literalValues : Array V10Wide 4#usize) (currentValues : Array AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact 4#usize)
      (a : Array Std.U8 608#usize) (v0 v1 v2 v3 : AspisR1FastDotsCurrent.aspis_core.field.wide_exact.WideExact),
      literalV10Outer concreteOps q input = .ok literalValues ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots_fixed concreteOps q
        (mapWideArray input) = .ok currentValues ∧
      mapArray
        AspisR1FastDotsV10CarrierMapV1.wideToEbyK literalValues = currentValues ∧
      a.val = q.val.slice 0 (608#usize) ∧
      (∀ x ∈ currentValues.val,
        AspisR1CurrentWide.Proof.CanonicalWide
          (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      currentValues.val = [v0,v1,v2,v3] ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
        a (mapWideArray input) 0#usize v0 ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
        a (mapWideArray input) 1#usize v1 ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
        a (mapWideArray input) 2#usize v2 ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps concreteOps)
        a (mapWideArray input) 3#usize v3 := by
  have h := literal_outer_total_and_field_results_from_scan
    concreteOps proof j q input gamma claimPowers hgamma hpowers hcaller
    hlen hj hread hscan
  have hinstall : AspisR1FastDotsFourCallbacksForwardRootV1.install concreteOps = concreteOps :=
    AspisR1FastDotsConcreteKernelOpsRootV1.installed_eq_concrete concreteOps
  simpa only [hinstall] using h

#print axioms concrete_literal_outer_total_and_field_results_from_scan

end AspisR1FastDotsConcreteV10CandidateEndpointV1
