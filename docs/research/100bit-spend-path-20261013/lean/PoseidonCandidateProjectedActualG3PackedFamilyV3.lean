import PoseidonCandidateProjectedActualG3PackedFamily
import PoseidonCandidateProjectedEvaluatorSourceV12
import SelectorAtPointModel

/-! Companion endpoint with no externally supplied boxed-point result: the
canonical point theorem constructs the actual boxed input, which is then fed
through the already checked G3 and packed-family composition. -/
set_option autoImplicit false
namespace AspisR1.PoseidonCandidateProjectedActualG3PackedFamilyV3
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe

abbrev QM := field.QM31
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Packed := Array QM 4#usize

/-- From canonical public openings and point arrays alone, the actual
`boxed_at_point` call succeeds and its result follows the G3 path to the
retained packed-family residual vector. The witness records both the boxed
call and the subsequent selector, internal, and projected source bindings. -/
theorem canonical_point_actual_boxed_g3_packed_family
    (openings : Openings) (point : Array QM 10#usize)
    (hpoint : AspisR1.SumHighInnerLoop.CanonicalArray point)
    (hopenZ : AspisR1.SumHighInnerLoop.CanonicalArray openings.z)
    (hopenSucc : AspisR1.SumHighInnerLoop.CanonicalArray openings.succ_z)
    (hopenXor : AspisR1.SumHighInnerLoop.CanonicalArray openings.xor12_z) :
    ∃ selectorInput : pool_v1.pair_forest_copy_terminal.Selectors,
      ∃ selectors : AspisR1.PoseidonCandidateProjectedActualG3.Selectors,
      ∃ internal : AspisR1.PoseidonCandidateProjectedActualG3.State,
      ∃ out : Packed,
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectorInput ∧
      AspisR1SelectedMaskProbe.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors = .ok out ∧
      AspisR1.PoseidonSelectorsSource.source selectorInput = .ok selectors ∧
      state_only_poseidon.interpolated_internal_pair openings.z selectors.local = .ok internal ∧
      AspisR1.PoseidonCandidateProjectedWrapperFactor.candidate_projected_source openings selectors = .ok out ∧
      (∀ i : Fin 4, AspisR1.PoseidonCandidateProjectedActualG3.Canonical
        (out.val[i.val]'(by simpa [out.property] using i.isLt))) ∧
      ∀ pub : R0P.Public AspisWideTower.WideExact,
        (R0P.poseidonPackedFamily
          (K := AspisWideTower.WideExact)
          AspisR1.ExtractedMaskSemanticBridgeConcrete.packBasis).residuals pub
          (AspisR1.ValueFamilyFieldTransport.mapOpenings
            AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
            (AspisR1.PoseidonSamePointResidualModel.decodedOpenings openings))
          (fun b => AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
            (AspisR1.SelectorValueLaneModelComposition.pointSelector point b)) =
        List.ofFn (fun g : Fin 4 => AspisR1.ExtractedMaskSemanticBridgeConcrete.qm31ToWide
          (AspisR1.ExtractedMaskQM31Exact.decode
            (AspisR1.PoseidonClosure2ArrayExact.cell4 out g))) := by
  obtain ⟨selectorInput, hbox, _, _, _, _⟩ :=
    AspisR1.SelectorAtPointModel.boxed_at_point_products point hpoint
  obtain ⟨selectors, internal, out, hselectors, hinternal, hout, hcanonical, hfamily⟩ :=
    AspisR1.PoseidonCandidateProjectedActualG3PackedFamily.actual_boxed_candidate_g3_packed_family
      openings point selectorInput hpoint hopenZ hopenSucc hopenXor hbox
  have hevalEq := AspisR1SelectedMaskProbe.evaluator_qname_eq_factored openings selectors
  have heval : AspisR1SelectedMaskProbe.state_only_poseidon.evaluate_state_only_poseidon_oracle_projected
      openings selectors = .ok out := by
    rw [hevalEq, hout]
  exact ⟨selectorInput, selectors, internal, out,
    hbox, heval, hselectors, hinternal, hout, hcanonical, hfamily⟩

#print axioms canonical_point_actual_boxed_g3_packed_family
end AspisR1.PoseidonCandidateProjectedActualG3PackedFamilyV3
