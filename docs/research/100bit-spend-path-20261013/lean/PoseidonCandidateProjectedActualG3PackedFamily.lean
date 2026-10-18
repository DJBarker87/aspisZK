import PoseidonCandidateProjectedActualG3
import AspisR1.PoseidonCandidatePackedFamilyResidual

/-! The final actual boxed G3 caller, now stated against the retained R0P
packed-family residual vector rather than a parallel scalar packing formula.
The leading/full/internal/projected operations and models are derived inside
ActualG3; this layer only changes the endpoint presentation. -/
set_option autoImplicit false
namespace AspisR1.PoseidonCandidateProjectedActualG3PackedFamily
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open R0P

abbrev QM := field.QM31
abbrev Wide := AspisWideTower.WideExact
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Packed := Array QM 4#usize
abbrev f := AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
abbrev PackB := AspisR1.ExtractedMaskSemanticBridgeConcrete.packBasis
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode

/-- The actual boxed candidate source path realizes the existing R0P packed
family residual vector over WideExact. Only canonical public inputs and the
source's actual boxed-point success are premises; all source result bindings
and packed-output canonicality are returned. -/
theorem actual_boxed_candidate_g3_packed_family
    (openings : Openings) (point : Array QM 10#usize)
    (selectorInput : pool_v1.pair_forest_copy_terminal.Selectors)
    (hpoint : AspisR1.SumHighInnerLoop.CanonicalArray point)
    (hopenZ : AspisR1.SumHighInnerLoop.CanonicalArray openings.z)
    (hopenSucc : AspisR1.SumHighInnerLoop.CanonicalArray openings.succ_z)
    (hopenXor : AspisR1.SumHighInnerLoop.CanonicalArray openings.xor12_z)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectorInput) :
    ∃ selectors : AspisR1.PoseidonCandidateProjectedActualG3.Selectors,
      ∃ internal : AspisR1.PoseidonCandidateProjectedActualG3.State,
      ∃ out : Packed,
      AspisR1.PoseidonSelectorsSource.source selectorInput = .ok selectors ∧
      state_only_poseidon.interpolated_internal_pair openings.z selectors.local = .ok internal ∧
      AspisR1.PoseidonCandidateProjectedWrapperFactor.candidate_projected_source openings selectors = .ok out ∧
      (∀ i : Fin 4, AspisR1.PoseidonCandidateProjectedActualG3.Canonical
        (out.val[i.val]'(by simpa [out.property] using i.isLt))) ∧
      ∀ pub : Public Wide,
        (poseidonPackedFamily (K := Wide) PackB).residuals pub
          (AspisR1.ValueFamilyFieldTransport.mapOpenings f
            (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings))
          (fun b => f (pointSelector point b)) =
        List.ofFn (fun g : Fin 4 => f (Decode (AspisR1.PoseidonClosure2ArrayExact.cell4 out g))) := by
  obtain ⟨selectors, internal, out, hselectors, hinternal, hout, hcanonical, hformula⟩ :=
    AspisR1.PoseidonCandidateProjectedActualG3.actual_boxed_candidate_g3
      openings point selectorInput hpoint hopenZ hopenSucc hopenXor hbox
  refine ⟨selectors, internal, out, hselectors, hinternal, hout, hcanonical, ?_⟩
  intro pub
  have hfamily := @AspisR1.PoseidonCandidatePackedFamilyResidual.packed_family_formula
    Wide _ _ PackB pub
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

#print axioms actual_boxed_candidate_g3_packed_family
end
end AspisR1.PoseidonCandidateProjectedActualG3PackedFamily
