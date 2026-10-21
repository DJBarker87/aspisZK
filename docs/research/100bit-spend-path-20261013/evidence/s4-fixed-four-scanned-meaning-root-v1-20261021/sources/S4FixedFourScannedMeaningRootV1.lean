import S4WholeOuterTransferRootV1
import S4ScannedAcceptedRunRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsFixedFourScannedMeaningRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1FastDotsForwardLiteralValueRootV1 (literalOps)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)
open AspisR1FastDotsClaimPowerCoordinateBridgeV1 (ClaimE ClaimCanonical claimArrayToFast)

theorem fixed_four_scanned_literal_values
    (base : Ops) (proof : Slice Std.U8) (j : Nat) (q : Slice Std.U8)
    (g : Array Wide 29#usize) (values : Array Wide 4#usize)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : g = claimArrayToFast claimPowers)
    (hlen : proof.val.length=57607) (hj : j<22)
    (hread : q.val=proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof=.ok true)
    (hfixed : AspisR1FastDotsCurrent.fast_dots.four_dots_fixed (install base) q g=.ok values) :
    ∃ (a : Array Std.U8 608#usize) (v0 v1 v2 v3 : Wide),
      a.val=q.val.slice 0 (608#usize) ∧
      (∀ x∈values.val,AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      values.val=[v0,v1,v2,v3] ∧
      LiteralFieldResult (literalOps base) a g 0#usize v0 ∧
      LiteralFieldResult (literalOps base) a g 1#usize v1 ∧
      LiteralFieldResult (literalOps base) a g 2#usize v2 ∧
      LiteralFieldResult (literalOps base) a g 3#usize v3 := by
  have hold := AspisR1FastDotsWholeOuterTransferRootV1.installed_fixed_four_success_old_four
    base q g values hfixed
  exact AspisR1FastDotsScannedAcceptedRunRootV1.scanned_accepted_run_literal_values
    base proof j q g values gamma claimPowers hgamma hpowers hcaller hlen hj hread hscan hold

#print axioms fixed_four_scanned_literal_values
end AspisR1FastDotsFixedFourScannedMeaningRootV1
