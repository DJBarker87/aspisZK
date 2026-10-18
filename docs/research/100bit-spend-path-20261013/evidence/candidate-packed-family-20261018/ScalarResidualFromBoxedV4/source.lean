import PoseidonCandidateProjectedBoxedPointExactV7
import PoseidonSamePointResidualModel

set_option autoImplicit false
namespace AspisR1.PoseidonCandidateProjectedScalarResidualFromBoxed
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (cell)
open AspisR1.PoseidonCandidateProjectedBoxedPointExact
open AspisR1.PoseidonCandidateProjectedWrapperFactor
open AspisR1.PoseidonSamePointResidualModel

abbrev QM := field.QM31
abbrev Exact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev State := AspisR1.PoseidonFullRoundCellStep.State
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := AspisR1.PoseidonSelectorsSource.Output
abbrev Packed := Array QM 4#usize
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector

/-- Compose the actual boxed selector/internal call path with the exact final
residual identity, leaving only the leading/full packed-output model boundary. -/
theorem boxed_candidate_actual_scalar_residual
    (openings : Openings) (point : Array QM 10#usize)
    (selectorInput : pool_v1.pair_forest_copy_terminal.Selectors)
    (leading full : Packed)
    (hpoint : AspisR1.SumHighInnerLoop.CanonicalArray point)
    (hopenZ : AspisR1.SumHighInnerLoop.CanonicalArray openings.z)
    (hopenSucc : AspisR1.SumHighInnerLoop.CanonicalArray openings.succ_z)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectorInput)
    (hleadingCall : state_only_poseidon.leading_pair_packed openings = .ok leading)
    (hfullCall : state_only_poseidon.interpolated_full_pair_packed openings.z selectorInput.low = .ok full)
    (hleadingCanonical : ∀ i : Fin 4, Canonical (leading.val[i.val]'(by simpa [leading.property] using i.isLt)))
    (hfullCanonical : ∀ i : Fin 4, Canonical (full.val[i.val]'(by simpa [full.property] using i.isLt)))
    (hleadingModel : ∀ g : Fin 4, Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 leading g) =
      R0P.poseidonPackingFormula iBasis uBasis (fun j =>
        R0P.poseidonLeadingPair (decodedOpenings openings).z (decodedOpenings openings).xor12 (lane g j)))
    (hfullModel : ∀ g : Fin 4, Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 full g) =
      R0P.poseidonPackingFormula iBasis uBasis (fun j =>
        R0P.poseidonInterpolatedFullPair (decodedOpenings openings).z
          (R0P.g2Low (pointSelector point)) (lane g j))) :
    ∃ selectors : Selectors, ∃ internal : State, ∃ out : Packed,
      AspisR1.PoseidonSelectorsSource.source selectorInput = .ok selectors ∧
      state_only_poseidon.interpolated_internal_pair openings.z selectors.local = .ok internal ∧
      candidate_projected_source openings selectors = .ok out ∧
      (∀ i : Fin 4, Canonical (out.val[i.val]'(by simpa [out.property] using i.isLt))) ∧
      ∀ g : Fin 4, Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 out g) =
        R0P.poseidonPackingFormula iBasis uBasis (fun j =>
          R0P.poseidonScalarResidual (decodedOpenings openings)
            (R0P.g2SumHigh (pointSelector point) 0 57 (by omega))
            (R0P.g2Low (pointSelector point)) (lane g j)) := by
  obtain ⟨selectors,internal,leadingLow,fullLow,internalLow,weights,out,
      hselectors,hinternalCall,hinternalModel,hweights,hleadingLow,hfullLow,
      hinternalLow,hout,houtCanonical,houtModel⟩ :=
    AspisR1.PoseidonCandidateProjectedBoxedPointExact.boxed_candidate_scalar_residual
      openings point selectorInput leading full hpoint hopenZ hopenSucc hbox
      hleadingCall hfullCall hleadingCanonical hfullCanonical
  obtain ⟨selectorsAgain,hsourceAgain,_,_,_,_,hlowSource⟩ :=
    AspisR1.PoseidonSelectorsSource.boxed_success point selectorInput hpoint hbox
  have hselectorsSame : selectorsAgain = selectors := by
    injection (hsourceAgain.symm.trans hselectors)
  subst selectorsAgain
  have hlocal : (fun i : Fin 16 => Decode (cell selectors.local i)) =
      R0P.g2Low (pointSelector point) := by
    funext i
    have hi : i.val < (16#usize).val := by simpa using i.isLt
    have h := hlowSource i
    dsimp only [AspisR1.SelectorExpansionCorrectness.decodedArray,
      AspisR1.SelectorExpansionCorrectness.decodedAt] at h
    rw [dif_pos hi] at h
    exact h
  have hinternal : ∀ j : Fin 16,
      decodedState internal j = R0P.poseidonInterpolatedInternalPair
        (decodedOpenings openings).z (R0P.g2Low (pointSelector point)) j := by
    intro j
    have h := hinternalModel j
    change Decode (cell internal j) = _ at h
    have hopening : (fun i : Fin 16 => Decode (cell openings.z i)) =
        (decodedOpenings openings).z := rfl
    rw [hopening, hlocal] at h
    exact h
  refine ⟨selectors,internal,out,hselectors,hinternalCall,hout,houtCanonical,?_⟩
  intro g
  have hmodel := AspisR1.PoseidonSamePointResidualModel.same_point_model_eq
      openings point internal leading full hleadingModel hfullModel hinternal g
  exact (houtModel g).trans hmodel

#print axioms boxed_candidate_actual_scalar_residual
end AspisR1.PoseidonCandidateProjectedScalarResidualFromBoxed
