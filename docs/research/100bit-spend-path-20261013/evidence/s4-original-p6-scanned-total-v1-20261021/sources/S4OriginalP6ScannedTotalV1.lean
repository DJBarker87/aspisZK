import S4TotalScannedFieldResultsRootV1
import S4WholeOuterTransferRootV1
import S4V10TypedInnerBodyOpsV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsOriginalP6ScannedTotalV1

open AspisR1FastDotsTotalScannedFieldResultsRootV1 (fixed_four_total_and_field_results_from_scan)
open AspisR1FastDotsWholeOuterTransferRootV1 (installed_fixed_four_success_old_four)
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1FastDotsV10TypedInnerBodyOpsV1 (mapWideArray)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
  (ClaimE ClaimCanonical claimArrayToFast)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)

abbrev V10Wide := AspisR1FastDotsMinimalFixedCallsV10.aspis_core.field.wide_exact.WideExact

/-- The scanner-derived fixed-helper result transfers to the exact original
extracted/P6 `four_dots` operation on the same coefficient array and output.
The same four field-result witnesses from the scan are retained; no independent
fixed or P6 success premise is introduced.  P6/Rust-Std correspondence remains
an explicit source-library boundary. -/
theorem original_p6_four_total_and_field_results_from_scan
    (base : Ops) (proof : Slice Std.U8) (j : Nat) (q : Slice Std.U8)
    (input : Array V10Wide 29#usize)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : mapWideArray input = claimArrayToFast claimPowers)
    (hlen : proof.val.length = 57607) (hj : j < 22)
    (hread : q.val = proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    ∃ (values : Array Wide 4#usize) (a : Array Std.U8 608#usize) (v0 v1 v2 v3 : Wide),
      AspisR1FastDotsCurrent.fast_dots.four_dots (install base) q
        (mapWideArray input) = .ok values ∧
      a.val = q.val.slice 0 (608#usize) ∧
      (∀ x ∈ values.val,
        AspisR1CurrentWide.Proof.CanonicalWide
          (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      values.val = [v0,v1,v2,v3] ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps base)
        a (mapWideArray input) 0#usize v0 ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps base)
        a (mapWideArray input) 1#usize v1 ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps base)
        a (mapWideArray input) 2#usize v2 ∧
      LiteralFieldResult (AspisR1FastDotsForwardLiteralValueRootV1.literalOps base)
        a (mapWideArray input) 3#usize v3 := by
  obtain ⟨values, a, v0, v1, v2, v3, hfixed, ha, hcanonical,
      hvalues, h0, h1, h2, h3⟩ :=
    fixed_four_total_and_field_results_from_scan
      base proof j q (mapWideArray input) gamma claimPowers hgamma hpowers
      hcaller hlen hj hread hscan
  have hold := installed_fixed_four_success_old_four base q (mapWideArray input) values hfixed
  exact ⟨values, a, v0, v1, v2, v3, hold, ha, hcanonical, hvalues, h0, h1, h2, h3⟩

#print axioms original_p6_four_total_and_field_results_from_scan

end AspisR1FastDotsOriginalP6ScannedTotalV1
