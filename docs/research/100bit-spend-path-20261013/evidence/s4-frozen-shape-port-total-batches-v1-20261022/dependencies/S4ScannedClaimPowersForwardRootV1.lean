import S4ScannedOpeningForwardRootV1
import FourDotsClaimPowerCoordinateBridgeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1
namespace AspisR1FastDotsScannedClaimPowersForwardRootV1
open AspisR1FastDotsHeadLimbForwardRootV1 (Ops)
open AspisR1FastDotsHeadReadForwardRootV1 (Wide)
open AspisR1FastDotsFourCallbacksForwardRootV1 (install)
open AspisR1FastDotsForwardLiteralValueRootV1 (literalOps)
open AspisR1FastDotsLiteralCallbackValueRootV1 (LiteralFieldResult)
open AspisR1.MultiproofConeCanonical (bytesOf)
open AspisR1.OraclePortCompactDraft (openingCanonical scan slice)

theorem four_dots_forward_of_scanner_and_claim_powers
    (base : Ops) (proof : Slice Std.U8) (j : Nat) (q : Slice Std.U8)
    (a : Array Std.U8 608#usize) (g : Array Wide 29#usize)
    (gamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE)
    (claimPowers : Array AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE 29#usize)
    (hgamma : AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hcaller : g = AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimPowers)
    (hlen : proof.val.length=57607) (hj : j<22)
    (hread : q.val=proof.val.slice (10055+j*832) (10055+j*832+832))
    (hscan : MultiproofParserRef.parser_reference.scan proof=.ok true)
    (ha : a.val=q.val.slice 0 (608#usize))

    :
    ∃ (values : Array Wide 4#usize) (v0 v1 v2 v3 : Wide),
      AspisR1FastDotsCurrent.fast_dots.four_dots (install base) q g=.ok values ∧
      (∀ x∈values.val,AspisR1CurrentWide.Proof.CanonicalWide
        (AspisR1FastDotsTailWideAddCurrentV1.s4ToCurrentE x)) ∧
      values.val=[v0,v1,v2,v3] ∧
      LiteralFieldResult (literalOps base) a g 0#usize v0 ∧ LiteralFieldResult (literalOps base) a g 1#usize v1 ∧
      LiteralFieldResult (literalOps base) a g 2#usize v2 ∧ LiteralFieldResult (literalOps base) a g 3#usize v3 := by
  have hc := AspisR1FastDotsClaimPowerCoordinateBridgeV1.actual_fastdots_coordinate_bounds_of_claim_powers
    g gamma claimPowers hgamma hpowers hcaller
  exact AspisR1FastDotsScannedOpeningForwardRootV1.four_dots_forward_of_scanned_opening
    base proof j q a g hlen hj hread hscan ha hc

#print axioms four_dots_forward_of_scanner_and_claim_powers
end AspisR1FastDotsScannedClaimPowersForwardRootV1
