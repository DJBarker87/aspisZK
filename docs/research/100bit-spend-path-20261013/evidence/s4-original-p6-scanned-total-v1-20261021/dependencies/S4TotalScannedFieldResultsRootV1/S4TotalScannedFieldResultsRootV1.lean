import S4ConcreteReverseClosureRootV1
import S4FixedFourScannedMeaningRootV1
import S4ScannedClaimPowersForwardRootV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsTotalScannedFieldResultsRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1FastDotsForwardLiteralValueRootV1 (literalOps)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)

/-- Complete selected fixed-call arithmetic: the scanner and the same
canonical power array supply every domain witness. No successful dot call,
reverse-loop law, independent openingPrefix array or per-coordinate bound is assumed.
The concrete Rust/P6 source and caller bindings remain separate obligations. -/
theorem fixed_four_total_and_field_results_from_scan
    (base : Ops) (proof : Slice Std.U8) (j : Nat) (q : Slice Std.U8)
    (g : Array Wide 29#usize)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : g = claimArrayToFast claimPowers)
    (hlen : proof.val.length = 57607) (hj : j < 22)
    (hread : q.val = proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof = .ok true) :
    ∃ (values : Array Wide 4#usize) (a : Array Std.U8 608#usize) (v0 v1 v2 v3 : Wide),
      AspisR1FastDotsCurrent.fast_dots.four_dots_fixed (install base) q g = .ok values ∧
      a.val = q.val.slice 0 (608#usize) ∧
      (∀ x ∈ values.val, AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      values.val = [v0,v1,v2,v3] ∧
      LiteralFieldResult (literalOps base) a g 0#usize v0 ∧
      LiteralFieldResult (literalOps base) a g 1#usize v1 ∧
      LiteralFieldResult (literalOps base) a g 2#usize v2 ∧
      LiteralFieldResult (literalOps base) a g 3#usize v3 := by
  have hqLength : q.val.length = 832 := by
    rw [hread]
    simp only [List.slice,List.length_take,List.length_drop,hlen]
    omega
  let a : Array Std.U8 608#usize := ⟨q.val.take 608, by
    simp only [List.length_take,hqLength]
    decide⟩
  have ha : a.val = q.val.slice 0 (608#usize) := by simp only [a,List.slice,List.drop_zero]; rfl
  have hq : 608 ≤ q.length := by change 608 ≤ q.val.length; rw [hqLength]; decide
  have hopening := AspisR1FastDotsScannedOpeningForwardRootV1.strict_scan_accepted_opening
    proof j q hlen hj hread hscan
  have hpayload := AspisR1FastDotsCanonicalOpeningForwardRootV1.opening_payload_canonical q a ha hopening
  have hcoords := AspisR1FastDotsClaimPowerCoordinateBridgeV1.actual_fastdots_coordinate_bounds_of_claim_powers
    g gamma claimPowers hgamma hpowers hcaller
  obtain ⟨values,hfixed,_hcan⟩ :=
    AspisR1FastDotsConcreteReverseClosureRootV1.fixed_four_total_on_slots
      base q a g hq ha hcoords (fun slot hs =>
        AspisR1FastDotsCanonicalSlotInputsRootV1.canonical_slot_input a g slot hs hpayload)
  obtain ⟨openingPrefix,v0,v1,v2,v3,hprefix,hcan,hvalues,h0,h1,h2,h3⟩ :=
    AspisR1FastDotsFixedFourScannedMeaningRootV1.fixed_four_scanned_literal_values
      base proof j q g values gamma claimPowers hgamma hpowers hcaller hlen hj hread hscan hfixed
  exact ⟨values,openingPrefix,v0,v1,v2,v3,hfixed,hprefix,hcan,hvalues,h0,h1,h2,h3⟩

#print axioms fixed_four_total_and_field_results_from_scan
end AspisR1FastDotsTotalScannedFieldResultsRootV1
