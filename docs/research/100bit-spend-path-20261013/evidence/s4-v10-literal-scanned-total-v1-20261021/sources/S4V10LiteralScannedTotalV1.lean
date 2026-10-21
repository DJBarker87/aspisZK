import S4TotalScannedFieldResultsRootV1
import S4V10LiteralOuterTransferRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsV10LiteralScannedTotalV1

open AspisR1FastDotsTotalScannedFieldResultsRootV1 (fixed_four_total_and_field_results_from_scan)
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1FastDotsV10LiteralOuterTransferRootV1
  (literalV10Outer literal_outer_to_current)
open AspisR1FastDotsV10TypedInnerBodyOpsV1 (mapWideArray)
open AspisR1S4FourWrapperCarrierTransportRootV1 (mapArray)
open AspisR1FastDotsV10CarrierMapV1 (wideToEbyK)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
  (ClaimE ClaimCanonical claimArrayToFast)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)

abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact

/-- The scanner/canonical-power theorem supplies fixed-helper success and
all four literal field-result witnesses.  The checked all-Result V10 transport
then derives success of the corresponding literal typed outer call and maps
its exact four outputs back to that same array.  The caller, scanner, query
slice, and ClaimPowers premises are shared; no slot-success or outer-call
success premise is added.  This remains a selected P6/model result, not frozen
Rust standard-library correspondence or production adoption. -/
theorem literal_outer_total_and_field_results_from_scan
    (base : Ops) (proof : Slice Std.U8) (j : Nat) (q : Slice Std.U8)
    (input : Array V10Wide 29#usize)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : mapWideArray input = claimArrayToFast claimPowers)
    (hlen : proof.val.length = 57607) (hj : j < 22)
    (hread : q.val = proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    ∃ (literalValues : Array V10Wide 4#usize) (currentValues : Array Wide 4#usize)
      (a : Array Std.U8 608#usize) (v0 v1 v2 v3 : Wide),
      literalV10Outer (install base) q input = .ok literalValues ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots_fixed (install base) q
        (mapWideArray input) = .ok currentValues ∧
      mapArray wideToEbyK literalValues = currentValues ∧
      a.val = q.val.slice 0 (608#usize) ∧
      (∀ x ∈ currentValues.val,
        AspisR1CurrentWide.Proof.CanonicalWide
          (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      currentValues.val = [v0,v1,v2,v3] ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps base)
        a (mapWideArray input) 0#usize v0 ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps base)
        a (mapWideArray input) 1#usize v1 ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps base)
        a (mapWideArray input) 2#usize v2 ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps base)
        a (mapWideArray input) 3#usize v3 := by
  obtain ⟨currentValues, a, v0, v1, v2, v3, hfixed, ha, hcanonical,
      hvalues, h0, h1, h2, h3⟩ :=
    fixed_four_total_and_field_results_from_scan
      base proof j q (mapWideArray input) gamma claimPowers hgamma hpowers
      hcaller hlen hj hread hscan
  have htransport := literal_outer_to_current (install base) q input
  rw [hfixed] at htransport
  cases hliteral : literalV10Outer (install base) q input with
  | ok literalValues =>
      simp only [AspisR1FastDotsV10TailMapRootV1.mapRes, hliteral] at htransport
      have hmap : mapArray wideToEbyK literalValues = currentValues :=
        Result.ok.inj htransport
      exact ⟨literalValues, currentValues, a, v0, v1, v2, v3,
        rfl, hfixed, hmap, ha, hcanonical, hvalues, h0, h1, h2, h3⟩
  | fail err =>
      simp [AspisR1FastDotsV10TailMapRootV1.mapRes, hliteral] at htransport
  | div =>
      simp [AspisR1FastDotsV10TailMapRootV1.mapRes, hliteral] at htransport

#print axioms literal_outer_total_and_field_results_from_scan

end AspisR1FastDotsV10LiteralScannedTotalV1
