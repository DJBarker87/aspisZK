import S4QueryValuesFourCallbackClaimPowersV1
import AspisR1QueryPrefixToCurrentFourDotsV1
import FourDotsClaimPowerCoordinateBridgeV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1FastDotsQueryValuesClaimPrefixCarrierV1

open AspisR1QueryPrefixToCurrentFourDotsV1
open AspisR1FastDotsClaimPowerCoordinateBridgeV1
abbrev PrefixWide := AspisR1QueryPrefixToCurrentFourDotsV1.PrefixWide
abbrev CurrentWide := AspisR1QueryPrefixToCurrentFourDotsV1.CurrentWide
abbrev ClaimE := AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimE
abbrev ClaimCanonical := AspisR1FastDotsClaimPowerCoordinateBridgeV1.ClaimCanonical
abbrev CoordBound := AspisR1FastDotsClaimPowerCoordinateBridgeV1.CoordBound

/-- Map a successful canonical ClaimPowers output into the exact S8 query
    coefficient carrier by the two already explicit coordinate transports. -/
def claimToPrefix (x : ClaimE) : PrefixWide :=
  currentWideToPrefix (claimToFast x)

def claimArrayToPrefix (xs : Array ClaimE 29#usize) : Array PrefixWide 29#usize :=
  ⟨xs.val.map claimToPrefix, by simpa only [List.length_map] using xs.property⟩

theorem prefixWideToCurrent_currentWideToPrefix (x : CurrentWide) :
    prefixWideToCurrent (currentWideToPrefix x) = x := by
  cases x with
  | mk c0 c1 =>
    cases c0 with
    | mk c00 c01 =>
      cases c00 with
      | mk a b => cases c01 with | mk c d =>
        cases c1 with
        | mk c10 c11 =>
          cases c10 with
          | mk e f => cases c11 with | mk g h => rfl

theorem prefixArrayToCurrent_claimArrayToPrefix
    (xs : Array ClaimE 29#usize) :
    prefixArrayToCurrent (claimArrayToPrefix xs) = claimArrayToFast xs := by
  cases xs with
  | mk values hlen =>
    simp only [claimArrayToPrefix, prefixArrayToCurrent, claimArrayToFast,
      List.map_map, Function.comp_def]
    congr 1

/-- A concrete successful ClaimPowers result, mapped into the exact S8 prefix
    array carrier, supplies the S4 coordinate bounds for that same array.
    The caller still has to establish that its `g` is this mapped result. -/
theorem claim_powers_prefix_array_coordinate_bounds
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers) :
    ∀ i : Fin 29,
      CoordBound ((prefixArrayToCurrent (claimArrayToPrefix claimPowers)).val[i.val]'(by scalar_tac)) := by
  intro i
  have hclaim := claim_powers_array_coordinate_bounds gamma claimPowers hgamma hpowers i
  simpa only [prefixArrayToCurrent_claimArrayToPrefix] using hclaim

/-- With an exact caller array equation, the previous four-callback consumer
    needs no arbitrary pointwise coordinates and no separate carrier identity
    premise. The remaining equation is precisely the tx2/query-loop source
    g-origin boundary documented in the packet. -/
theorem query_values_success_four_callback_field_results_of_claim_powers_prefix
    (openingOp : AspisR1QueryPrefixToCurrentFourDotsV1.PrefixOpeningOp)
    (base : AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1.Ops) (proof : Slice Std.U8)
    (p : AspisR1Stage2QueryTailCut.verifier.Prepared)
    (a : AspisR1Stage2QueryTailCut.verifier.Accumulator)
    (g : Array PrefixWide 29#usize)
    (gamma : ClaimE) (claimPowers : Array ClaimE 29#usize)
    (hgamma : ClaimCanonical gamma)
    (hpowers : AspisR1CurrentPreparedClaim.ClaimPowers.powers 29#usize gamma = .ok claimPowers)
    (hg : g = claimArrayToPrefix claimPowers)
    (obs : Option (AspisR1Stage2QueryTailCut.verifier.Phase → Result Unit))
    (geometry : AspisR1Stage2QueryTailCut.verifier.QueryGeometry)
    (pending : AspisR1Stage2QueryTailCut.verifier.BatchedWeights)
    {out : core.result.Result
      (Std.Usize × Std.Usize × Slice Std.U8 × Array PrefixWide 4#usize)
      AspisR1Stage2QueryTailCut.verifier.Error}
    (h : AspisR1Stage2QueryTailCut.query_values_forward_prefix_ops
      openingOp
      (AspisR1QueryPrefixToCurrentFourDotsV1.currentFourDotsAsPrefix
        (AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1.Outer base))
      proof p a g obs geometry pending = .ok out) :
    ∃ (i : Std.U32) (u : Std.Usize) (q : Slice Std.U8)
      (dots : Array CurrentWide 4#usize) (arrayQ : Array Std.U8 608#usize)
      (v0 v1 v2 v3 : CurrentWide),
      Array.index_usize p.queries a.next = .ok i ∧
      lift (UScalar.cast .Usize i) = .ok u ∧ openingOp proof a.next = .ok q ∧
      AspisR1FastDotsCurrent.fast_dots.four_dots
        (AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1.Outer base) q
        (prefixArrayToCurrent g) = .ok dots ∧
      out = core.result.Result.Ok (a.next, u, q, currentArrayToPrefix dots) ∧
      arrayQ.val = q.val.slice 0 (608#usize) ∧ dots.val = [v0,v1,v2,v3] ∧
      AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1.CallbackFieldResult base
        (AspisR1FastDotsConcreteTailInstallRootV1.install
          (AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1.Outer base)) arrayQ
          (prefixArrayToCurrent g) 0#usize v0 ∧
      AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1.CallbackFieldResult base
        (AspisR1FastDotsConcreteTailInstallRootV1.install
          (AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1.Outer base)) arrayQ
          (prefixArrayToCurrent g) 1#usize v1 ∧
      AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1.CallbackFieldResult base
        (AspisR1FastDotsConcreteTailInstallRootV1.install
          (AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1.Outer base)) arrayQ
          (prefixArrayToCurrent g) 2#usize v2 ∧
      AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1.CallbackFieldResult base
        (AspisR1FastDotsConcreteTailInstallRootV1.install
          (AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1.Outer base)) arrayQ
          (prefixArrayToCurrent g) 3#usize v3 := by
  have harray : prefixArrayToCurrent g = claimArrayToFast claimPowers := by
    rw [hg]
    exact prefixArrayToCurrent_claimArrayToPrefix claimPowers
  exact AspisR1FastDotsQueryValuesFourCallbackClaimPowersV1.query_values_success_four_callback_field_results_of_claim_powers
    openingOp base proof p a g gamma claimPowers hgamma hpowers harray obs geometry pending h

#print axioms prefixWideToCurrent_currentWideToPrefix
#print axioms prefixArrayToCurrent_claimArrayToPrefix
#print axioms claim_powers_prefix_array_coordinate_bounds
#print axioms query_values_success_four_callback_field_results_of_claim_powers_prefix

end AspisR1FastDotsQueryValuesClaimPrefixCarrierV1
