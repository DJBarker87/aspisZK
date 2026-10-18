import PoseidonCandidateProjectedScalarResidualWideCompositionV3
import PathFamilyFieldTransport
import R0P.Poseidon

set_option autoImplicit false
namespace AspisR1.PoseidonCandidatePackedFamilyResidual
noncomputable section
open AspisV8R15.ExactTowerBase
open Aeneas Aeneas.Std Result
open R0P
open AspisR1SelectedMaskProbe

abbrev Wide := AspisWideTower.WideExact
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev f := AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
abbrev PackB := AspisR1.ExtractedMaskSemanticBridgeConcrete.packBasis
abbrev lane := AspisR1.PoseidonExternalPackedModel.lane
abbrev Openings := AspisR1.PoseidonCandidateProjectedScalarResidualWide.Openings
abbrev Packed := AspisR1.PoseidonCandidateProjectedScalarResidualWide.Packed
abbrev pointSelector := AspisR1.PoseidonCandidateProjectedScalarResidualWide.pointSelector

/-- Symbolic definition bridge: the family’s four packed residuals are exactly
its four explicit basis packing formulas. This is generic in the field and
basis; no concrete packed numeral is normalized. -/
theorem packed_family_formula {K : Type} [Field K] {F : Subfield K}
    (B : PackBasis F) (pub : Public K) (o : R0P.Openings K) (sel : R0P.Sel K) :
    (poseidonPackedFamily B).residuals pub o sel =
      List.ofFn (fun group : Fin 4 =>
        poseidonPackingFormula B.i B.u (fun limb : Fin 4 =>
          poseidonScalarResidual o (g2SumHigh sel 0 57 (by omega))
            (g2Low sel) ⟨4 * group.val + limb.val, by omega⟩)) := by
  rfl

/-- The four actual boxed candidate outputs instantiate the retained R0P
`poseidonPackedFamily` residual vector over WideExact. The output bindings and
canonicality from the actual source theorem are retained. -/
theorem boxed_candidate_is_packed_family
    (openings : Openings) (point : Array (field.QM31) 10#usize)
    (selectorInput : pool_v1.pair_forest_copy_terminal.Selectors)
    (leading full : Packed)
    (hpoint : AspisR1.SumHighInnerLoop.CanonicalArray point)
    (hopenZ : AspisR1.SumHighInnerLoop.CanonicalArray openings.z)
    (hopenSucc : AspisR1.SumHighInnerLoop.CanonicalArray openings.succ_z)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectorInput)
    (hleadingCall : state_only_poseidon.leading_pair_packed openings = .ok leading)
    (hfullCall : state_only_poseidon.interpolated_full_pair_packed openings.z selectorInput.low = .ok full)
    (hleadingCanonical : ∀ i : Fin 4, AspisR1.PoseidonCandidateProjectedScalarResidualFromBoxed.Canonical
      (leading.val[i.val]'(by simpa [leading.property] using i.isLt)))
    (hfullCanonical : ∀ i : Fin 4, AspisR1.PoseidonCandidateProjectedScalarResidualFromBoxed.Canonical
      (full.val[i.val]'(by simpa [full.property] using i.isLt)))
    (hleadingModel : ∀ g : Fin 4, AspisR1.PoseidonCandidateProjectedScalarResidualWide.Decode
      (AspisR1.PoseidonClosure2ArrayExact.cell4 leading g) =
      poseidonPackingFormula AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis
        AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis (fun j =>
          poseidonLeadingPair
            (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings).z
            (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings).xor12
            (lane g j)))
    (hfullModel : ∀ g : Fin 4, AspisR1.PoseidonCandidateProjectedScalarResidualWide.Decode
      (AspisR1.PoseidonClosure2ArrayExact.cell4 full g) =
      poseidonPackingFormula AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis
        AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis (fun j =>
          poseidonInterpolatedFullPair
            (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings).z
            (g2Low (pointSelector point)) (lane g j))) :
    ∃ selectors : AspisR1.PoseidonCandidateProjectedScalarResidualWide.Selectors,
      ∃ internal : AspisR1.PoseidonCandidateProjectedScalarResidualWide.State,
      ∃ out : Packed,
      AspisR1.PoseidonSelectorsSource.source selectorInput = .ok selectors ∧
      state_only_poseidon.interpolated_internal_pair openings.z selectors.local = .ok internal ∧
      AspisR1.PoseidonCandidateProjectedWrapperFactor.candidate_projected_source openings selectors = .ok out ∧
      (∀ i : Fin 4, AspisR1.PoseidonCandidateProjectedScalarResidualFromBoxed.Canonical
        (out.val[i.val]'(by simpa [out.property] using i.isLt))) ∧
      ∀ pub : Public Wide,
        (poseidonPackedFamily (K := Wide) PackB).residuals pub
          (AspisR1.ValueFamilyFieldTransport.mapOpenings f
            (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings))
          (fun b => f (pointSelector point b)) =
        List.ofFn (fun g : Fin 4 =>
          f (AspisR1.PoseidonCandidateProjectedScalarResidualWide.Decode
            (AspisR1.PoseidonClosure2ArrayExact.cell4 out g))) := by
  obtain ⟨selectors, internal, out, hselectors, hinternal, hout, hcanonical, hformula⟩ :=
    AspisR1.PoseidonCandidateProjectedScalarResidualWide.boxed_candidate_actual_wide_scalar_residual
      openings point selectorInput leading full hpoint hopenZ hopenSucc hbox
      hleadingCall hfullCall hleadingCanonical hfullCanonical hleadingModel hfullModel
  refine ⟨selectors, internal, out, hselectors, hinternal, hout, hcanonical, ?_⟩
  intro pub
  have hfamily := @packed_family_formula Wide _ _ PackB pub
    (AspisR1.ValueFamilyFieldTransport.mapOpenings f
      (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings))
    (fun b => f (pointSelector point b))
  rw [hfamily]
  apply congrArg List.ofFn
  funext g
  have hsum := AspisR1.PathFamilyFieldTransport.map_sumHigh f (pointSelector point) 0 57 (by omega)
  have hlow : AspisR1.PoseidonMap.mapState f (g2Low (pointSelector point)) =
      g2Low (fun b => f (pointSelector point b)) := by
    funext l
    change f (g2Low (pointSelector point) l) =
      g2Low (fun b => f (pointSelector point b)) l
    exact AspisR1.PathFamilyFieldTransport.map_low f (pointSelector point) l
  have hg := hformula g
  rw [hsum, hlow] at hg
  exact hg.symm

#print axioms packed_family_formula
#print axioms boxed_candidate_is_packed_family
end
end AspisR1.PoseidonCandidatePackedFamilyResidual
