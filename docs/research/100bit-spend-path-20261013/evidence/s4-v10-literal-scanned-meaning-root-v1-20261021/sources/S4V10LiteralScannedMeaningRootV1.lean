import S4V10LiteralOuterTransferRootV1
import S4FixedFourScannedMeaningRootV1
import S4ScannedAcceptedRunRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsV10LiteralScannedMeaningRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1FastDotsForwardLiteralValueRootV1 (literalOps)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)

open AspisR1FastDotsV10TypedInnerBodyOpsV1 (mapWideArray)
open AspisR1S4FourWrapperCarrierTransportRootV1 (mapArray)
open AspisR1FastDotsV10CarrierMapV1 (wideToEbyK)
abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact

theorem literal_four_scanned_literal_values
    (base : Ops) (proof : Slice Std.U8) (j : Nat) (q : Slice Std.U8)
    (input : Array V10Wide 29#usize) (output : Array V10Wide 4#usize)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : mapWideArray input = claimArrayToFast claimPowers)
    (hlen : proof.val.length=57607) (hj : j<22)
    (hread : q.val=proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof=.ok true)
    (hcall : AspisR1FastDotsV10LiteralOuterTransferRootV1.literalV10Outer
      (install base) q input = .ok output) :
    ∃ (a : Array Std.U8 608#usize) (v0 v1 v2 v3 : Wide),
      a.val=q.val.slice 0 (608#usize) ∧
      (∀ x∈(mapArray wideToEbyK output).val,AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      (mapArray wideToEbyK output).val=[v0,v1,v2,v3] ∧
      LiteralFieldResult (literalOps base) a (mapWideArray input) 0#usize v0 ∧
      LiteralFieldResult (literalOps base) a (mapWideArray input) 1#usize v1 ∧
      LiteralFieldResult (literalOps base) a (mapWideArray input) 2#usize v2 ∧
      LiteralFieldResult (literalOps base) a (mapWideArray input) 3#usize v3 := by
  have hfixed := AspisR1FastDotsV10LiteralOuterTransferRootV1.literal_outer_success_current
    (install base) q input output hcall
  exact AspisR1FastDotsFixedFourScannedMeaningRootV1.fixed_four_scanned_literal_values
    base proof j q (mapWideArray input) (mapArray wideToEbyK output)
    gamma claimPowers hgamma hpowers hcaller hlen hj hread hscan hfixed

#print axioms literal_four_scanned_literal_values
end AspisR1FastDotsV10LiteralScannedMeaningRootV1
