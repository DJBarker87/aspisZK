import AspisR1.PoseidonSelectorsSource
import PoseidonLeadingPairExact
import PoseidonInterpolatedFullPairExact
import PoseidonCandidateProjectedScalarResidualWideCompositionV3

/-! Actual boxed candidate caller composition. Only canonical input arrays and
boxed_at_point success are premises; leading/full/internal calls and output
model are derived through their exact source consumers. -/
set_option autoImplicit false
namespace AspisR1.PoseidonCandidateProjectedActualG3
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (cell)
open AspisR1.PoseidonExternalPackedGroupCall (Packed packedCell packedCanonical)
open AspisR1.PoseidonCandidateProjectedScalarResidualFromBoxed
open AspisR1.PoseidonCandidateProjectedScalarResidualWide
open AspisR1.PoseidonSamePointResidualModel

abbrev QM := field.QM31
abbrev Exact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev State := AspisR1.PoseidonFullRoundCellStep.State
abbrev CanonicalState := AspisR1.PoseidonFullRoundCellStep.CanonicalState
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := AspisR1.PoseidonSelectorsSource.Output
abbrev Packed := Array QM 4#usize
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev lane := AspisR1.PoseidonExternalPackedModel.lane

/-- Actual final G3 composition from the boxed point through the leading,
interpolated-full, internal, and projected candidate sources to the retained
R0P residual in concrete WideExact packing form. -/
theorem actual_boxed_candidate_g3
    (openings : Openings) (point : Array QM 10#usize)
    (selectorInput : pool_v1.pair_forest_copy_terminal.Selectors)
    (hpoint : AspisR1.SumHighInnerLoop.CanonicalArray point)
    (hopenZ : AspisR1.SumHighInnerLoop.CanonicalArray openings.z)
    (hopenSucc : AspisR1.SumHighInnerLoop.CanonicalArray openings.succ_z)
    (hopenXor : AspisR1.SumHighInnerLoop.CanonicalArray openings.xor12_z)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectorInput) :
    ∃ selectors : Selectors, ∃ internal : State, ∃ out : Packed,
      AspisR1.PoseidonSelectorsSource.source selectorInput = .ok selectors ∧
      state_only_poseidon.interpolated_internal_pair openings.z selectors.local = .ok internal ∧
      AspisR1.PoseidonCandidateProjectedWrapperFactor.candidate_projected_source openings selectors = .ok out ∧
      (∀ i : Fin 4, Canonical (out.val[i.val]'(by simpa [out.property] using i.isLt))) ∧
      ∀ g : Fin 4, AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
        (Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 out g)) =
        R0P.poseidonPackingFormula AspisR1.ExtractedMaskSemanticBridgeConcrete.packBasis.i
          AspisR1.ExtractedMaskSemanticBridgeConcrete.packBasis.u (fun j =>
          R0P.poseidonScalarResidual
            (AspisR1.ValueFamilyFieldTransport.mapOpenings
              AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
              (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings))
            (AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
              (R0P.g2SumHigh (pointSelector point) 0 57 (by omega)))
            (AspisR1.PoseidonMap.mapState AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
              (R0P.g2Low (pointSelector point))) (lane g j)) := by
  have hz : CanonicalState openings.z := by
    intro i
    exact hopenZ i
  have hs : CanonicalState openings.succ_z := by
    intro i
    exact hopenSucc i
  have hx : CanonicalState openings.xor12_z := by
    intro i
    exact hopenXor i
  obtain ⟨selectors0,hselectors0,hblockCan,hlocalCan,hlocals,hblockModel,hlowModel⟩ :=
    AspisR1.PoseidonSelectorsSource.boxed_success point selectorInput hpoint hbox
  have hlocalState : CanonicalState selectors0.local := by
    intro i
    exact hlocalCan i
  obtain ⟨leading,hleadingCall,hleadingPackedCan,hleadingModel0⟩ :=
    AspisR1.PoseidonLeadingPairExact.source_success openings hz hx
  obtain ⟨full,hfullCall0,hfullPackedCan,hfullModel0⟩ :=
    AspisR1.PoseidonInterpolatedFullPairExact.qm_source_success openings.z selectors0.local
      hz hlocalState
  have hfullCall : state_only_poseidon.interpolated_full_pair_packed openings.z selectorInput.low = .ok full := by
    rw [hlocals] at hfullCall0
    exact hfullCall0
  have hleadingCan : ∀ i : Fin 4, Canonical
      (leading.val[i.val]'(by simpa [leading.property] using i.isLt)) := by
    intro i
    have h := hleadingPackedCan i
    change Canonical (leading.val[i.val]'(by simpa [leading.property] using i.isLt)) at h
    exact h
  have hfullCan : ∀ i : Fin 4, Canonical
      (full.val[i.val]'(by simpa [full.property] using i.isLt)) := by
    intro i
    have h := hfullPackedCan i
    change Canonical (full.val[i.val]'(by simpa [full.property] using i.isLt)) at h
    exact h
  have hleadingModel : ∀ g : Fin 4, Decode
      (AspisR1.PoseidonClosure2ArrayExact.cell4 leading g) =
      R0P.poseidonPackingFormula AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis
        AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis (fun j =>
          R0P.poseidonLeadingPair
            (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings).z
            (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings).xor12
            (lane g j)) := by
    intro g
    have h := hleadingModel0 g
    change Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 leading g) = _ at h
    exact h
  have hlow : (fun i : Fin 16 => Decode (cell selectors0.local i)) =
      R0P.g2Low (pointSelector point) := by
    funext i
    have hi : i.val < (16#usize).val := by simpa using i.isLt
    have h := hlowModel i
    dsimp only [AspisR1.SelectorExpansionCorrectness.decodedArray,
      AspisR1.SelectorExpansionCorrectness.decodedAt] at h
    rw [dif_pos hi] at h
    exact h
  have hfullModel : ∀ g : Fin 4, Decode
      (AspisR1.PoseidonClosure2ArrayExact.cell4 full g) =
      R0P.poseidonPackingFormula AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis
        AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis (fun j =>
          R0P.poseidonInterpolatedFullPair
            (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings).z
            (R0P.g2Low (pointSelector point)) (lane g j)) := by
    intro g
    have h := hfullModel0 g
    change Decode (AspisR1.PoseidonExternalPackedGroupCall.packedCell full g) = _ at h
    have hstateZ : AspisR1.PoseidonInterpolatedFullPairExact.decodedState openings.z =
        (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings).z := rfl
    have hstateLocal : AspisR1.PoseidonInterpolatedFullPairExact.decodedState selectors0.local =
        R0P.g2Low (pointSelector point) := by
      funext i
      exact congrFun hlow i
    rw [hstateZ,hstateLocal] at h
    change Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 full g) = _ at h
    exact h
  obtain ⟨selectors,internal,out,hselectors,hinternalCall,hout,houtCanonical,hwideModel⟩ :=
    AspisR1.PoseidonCandidateProjectedScalarResidualWide.boxed_candidate_actual_wide_scalar_residual
      openings point selectorInput leading full hpoint hopenZ hopenSucc hbox
      hleadingCall hfullCall hleadingCan hfullCan hleadingModel hfullModel
  refine ⟨selectors,internal,out,hselectors,hinternalCall,hout,houtCanonical,?_⟩
  exact hwideModel

#print axioms actual_boxed_candidate_g3
end AspisR1.PoseidonCandidateProjectedActualG3
