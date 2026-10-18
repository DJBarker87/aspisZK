import PoseidonCandidateProjectedScalarResidualFromBoxedV4
import PoseidonCandidateScalarResidualWideV5

set_option autoImplicit false
namespace AspisR1.PoseidonCandidateProjectedScalarResidualWide
noncomputable section
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisR1SelectedMaskProbe
open R0P
open AspisR1.PoseidonCandidateProjectedScalarResidualFromBoxed

abbrev QM := field.QM31
abbrev Exact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Canonical := AspisR1.PoseidonCandidateProjectedScalarResidualFromBoxed.Canonical
abbrev f := AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
abbrev PackB := AspisR1.ExtractedMaskSemanticBridgeConcrete.packBasis
abbrev State := AspisR1.PoseidonFullRoundCellStep.State
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Selectors := AspisR1.PoseidonSelectorsSource.Output
abbrev Packed := Array QM 4#usize
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev lane := AspisR1.PoseidonExternalPackedModel.lane

/-- The boxed actual source path, with selector/internal/output bindings
retained, transported to the concrete WideExact packing formula. Only the
leading and full packed branch models remain explicit caller premises. -/
theorem boxed_candidate_actual_wide_scalar_residual
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
    (hfullCanonical : ∀ i : Fin 4, Canonical (full.val[i.val]'(by simpa [full.property] using i.isLt)) )
    (hleadingModel : ∀ g : Fin 4, Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 leading g) =
      R0P.poseidonPackingFormula AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis
        AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis (fun j =>
        R0P.poseidonLeadingPair
          (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings).z
          (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings).xor12
          (lane g j)))
    (hfullModel : ∀ g : Fin 4, Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 full g) =
      R0P.poseidonPackingFormula AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis
        AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis (fun j =>
        R0P.poseidonInterpolatedFullPair
          (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings).z
          (R0P.g2Low (pointSelector point)) (lane g j))) :
    ∃ selectors : Selectors, ∃ internal : State, ∃ out : Packed,
      AspisR1.PoseidonSelectorsSource.source selectorInput = .ok selectors ∧
      state_only_poseidon.interpolated_internal_pair openings.z selectors.local = .ok internal ∧
      AspisR1.PoseidonCandidateProjectedWrapperFactor.candidate_projected_source openings selectors = .ok out ∧
      (∀ i : Fin 4, Canonical (out.val[i.val]'(by simpa [out.property] using i.isLt))) ∧
      ∀ g : Fin 4, f (Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 out g)) =
        R0P.poseidonPackingFormula PackB.i PackB.u (fun j =>
          R0P.poseidonScalarResidual
            (AspisR1.ValueFamilyFieldTransport.mapOpenings f
              (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings))
            (f (R0P.g2SumHigh (pointSelector point) 0 57 (by omega)))
            (AspisR1.PoseidonMap.mapState f (R0P.g2Low (pointSelector point)))
            (lane g j)) := by
  obtain ⟨selectors,internal,out,hselectors,hinternalCall,hout,hcanonical,hexactModel⟩ :=
    AspisR1.PoseidonCandidateProjectedScalarResidualFromBoxed.boxed_candidate_actual_scalar_residual
      openings point selectorInput leading full hpoint hopenZ hopenSucc hbox
      hleadingCall hfullCall hleadingCanonical hfullCanonical hleadingModel hfullModel
  refine ⟨selectors,internal,out,hselectors,hinternalCall,hout,hcanonical,?_⟩
  intro g
  have hmap := congrArg f (hexactModel g)
  have htransport := AspisR1.PoseidonCandidateScalarResidualWide.map_scalar_residual_pack
      (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings)
      (R0P.g2SumHigh (pointSelector point) 0 57 (by omega))
      (R0P.g2Low (pointSelector point)) g
  exact hmap.trans htransport

#print axioms boxed_candidate_actual_wide_scalar_residual
end
end AspisR1.PoseidonCandidateProjectedScalarResidualWide
