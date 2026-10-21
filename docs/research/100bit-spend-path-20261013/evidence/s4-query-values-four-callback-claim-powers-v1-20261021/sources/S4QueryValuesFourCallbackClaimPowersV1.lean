import S4QueryValuesFourCallbackFieldResultV2
import FourDotsClaimPowerCoordinateBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1

abbrev PrefixWide := AspisR1QueryPrefixToCurrentFourDotsV1.PrefixWide
abbrev PrefixCM := AspisR1QueryPrefixToCurrentFourDotsV1.PrefixCM
abbrev PrefixQM := AspisR1QueryPrefixToCurrentFourDotsV1.PrefixQM
abbrev ClaimE := AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE
abbrev ClaimCanonical := AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimCanonical
abbrev ClaimCoordBound := AspisR1FastDotsClaimPowerCoordinateBridgeV1.CoordBound
abbrev CurrentWide := AspisR1FastDotsQueryValuesFourCallbackFieldResultV2.CurrentWide
abbrev Ops := AspisR1FastDotsQueryValuesFourCallbackFieldResultV2.Ops
abbrev Outer := AspisR1FastDotsQueryValuesFourCallbackFieldResultV2.Outer
abbrev CallbackFieldResult := AspisR1FastDotsQueryValuesFourCallbackFieldResultV2.CallbackFieldResult

/-- Replaces the 29 independent limb-coordinate premises in the caller join
    with successful canonical ClaimPowers plus the explicit fieldwise carrier
    identity for the same coefficient array.  The four source-field results
    remain opaque Prop witnesses from the checked caller theorem. -/
theorem query_values_success_four_callback_field_results_of_claim_powers
    (openingOp : AspisR1QueryPrefixToCurrentFourDotsV1.PrefixOpeningOp)
    (base : Ops) (proof : Slice Std.U8)
    (p : AspisR1Stage2QueryTailCut.verifier.Prepared)
    (a : AspisR1Stage2QueryTailCut.verifier.Accumulator)
    (g : Array PrefixWide 29#usize)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (harray : AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g =
      AspisR1FastDotsClaimPowerCoordinateBridgeV1.claimArrayToFast claimPowers)
    (obs : Option (AspisR1Stage2QueryTailCut.verifier.Phase → Result Unit))
    (geometry : AspisR1Stage2QueryTailCut.verifier.QueryGeometry)
    (pending : AspisR1Stage2QueryTailCut.verifier.BatchedWeights)
    {out : core.result.Result
      (Std.Usize × Std.Usize × Slice Std.U8 × Array PrefixWide 4#usize)
      AspisR1Stage2QueryTailCut.verifier.Error}
    (h : AspisR1Stage2QueryTailCut.query_values_forward_prefix_ops
      openingOp
      (AspisR1QueryPrefixToCurrentFourDotsV1.currentFourDotsAsPrefix (Outer base))
      proof p a g obs geometry pending = .ok out) :
    ∃ (i : Std.U32) (u : Std.Usize) (q : Slice Std.U8)
      (dots : Array CurrentWide 4#usize)
      (arrayQ : Array Std.U8 608#usize)
      (v0 v1 v2 v3 : CurrentWide),
      Array.index_usize p.queries a.next = .ok i ∧
      lift (UScalar.cast .Usize i) = .ok u ∧
      openingOp proof a.next = .ok q ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots (Outer base) q
        (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) = .ok dots ∧
      out = core.result.Result.Ok (a.next, u, q,
        AspisR1QueryPrefixToCurrentFourDotsV1.currentArrayToPrefix dots) ∧
      arrayQ.val = q.val.slice 0 (608#usize) ∧
      dots.val = [v0,v1,v2,v3] ∧
      CallbackFieldResult base
        (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base)) arrayQ
        (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) 0#usize v0 ∧
      CallbackFieldResult base
        (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base)) arrayQ
        (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) 1#usize v1 ∧
      CallbackFieldResult base
        (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base)) arrayQ
        (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) 2#usize v2 ∧
      CallbackFieldResult base
        (AspisR1FastDotsConcreteTailInstallRootV1.install (Outer base)) arrayQ
        (AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g) 3#usize v3 := by
  have hcoords : ∀ i : Fin 29,
      ClaimCoordBound ((AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent g).val[i.val]'(by
        simpa [AspisR1QueryPrefixToCurrentFourDotsV1.prefixArrayToCurrent, g.property] using i.isLt)) := by
    intro i
    have hclaim := AspisR1FastDotsClaimPowerCoordinateBridgeV1.claim_powers_array_coordinate_bounds
      gamma claimPowers hgamma hpowers i
    simpa only [harray] using hclaim
  exact AspisR1FastDotsQueryValuesFourCallbackFieldResultV2.query_values_success_four_callback_field_results
    openingOp base proof p a g hcoords obs geometry pending h

#print axioms query_values_success_four_callback_field_results_of_claim_powers

end AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1
