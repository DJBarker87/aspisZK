import AspisR1.PoseidonSelectorsSource
import PoseidonLeadingPairExact
import PoseidonInterpolatedFullPairExact
import PoseidonCandidateProjectedScalarResidualFromBoxedV4
import PoseidonCandidateProjectedEvaluatorSourceV12
/-! A callable Poseidon source-cut contract with every leading/full branch
constructed internally. Binding the retained source cut to frozen Rust is
separate; no native full-terminal result is claimed by this module. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPoseidonCallable55
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep (cell)
open AspisR1.PoseidonSamePointResidualModel
open AspisR1.ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)

abbrev QM := field.QM31
abbrev Exact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev CanonicalState := AspisR1.PoseidonFullRoundCellStep.CanonicalState
abbrev Openings := state_only_poseidon.StateOnlyPoseidonOpenings
abbrev pointSelector := AspisR1.SelectorValueLaneModelComposition.pointSelector
abbrev lane := AspisR1.PoseidonExternalPackedModel.lane

def model (point : Array QM 10#usize) (openings : Openings) (g : Fin 4) : Exact :=
  R0P.poseidonPackingFormula AspisR1.ExtractedMaskQmPackBase4Arithmetic.iBasis
    AspisR1.ExtractedMaskQmPackBase4Arithmetic.uBasis (fun j =>
    R0P.poseidonScalarResidual (decodedOpenings openings)
      (R0P.g2SumHigh (pointSelector point) 0 57 (by omega))
      (R0P.g2Low (pointSelector point)) (lane g j))

def run (openings : Openings) (selectorInput : pool_v1.pair_forest_copy_terminal.Selectors) :
    Result (Array QM 4#usize) := do
  let selectors ← AspisR1.PoseidonSelectorsSource.source selectorInput
  state_only_poseidon.evaluate_state_only_poseidon_oracle_projected openings selectors

theorem callable
    (openings : Openings) (point : Array QM 10#usize)
    (selectorInput : pool_v1.pair_forest_copy_terminal.Selectors)
    (hpoint : AspisR1.SumHighInnerLoop.CanonicalArray point)
    (hopenZ : AspisR1.SumHighInnerLoop.CanonicalArray openings.z)
    (hopenSucc : AspisR1.SumHighInnerLoop.CanonicalArray openings.succ_z)
    (hopenXor : AspisR1.SumHighInnerLoop.CanonicalArray openings.xor12_z)
    (hbox : pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point point = .ok selectorInput) :
    ∃ out : Array QM 4#usize, run openings selectorInput=.ok out ∧
      AspisR1.SumHighInnerLoop.CanonicalArray out ∧
      ∀ g : Fin 4, Decode (out.val[g.val]'(by simpa [out.property] using g.isLt))=model point openings g := by
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
  obtain ⟨selectors,internal,out,hselectors,hinternalCall,hout,houtCanonical,hmodel⟩ :=
    AspisR1.PoseidonCandidateProjectedScalarResidualFromBoxed.boxed_candidate_actual_scalar_residual
      openings point selectorInput leading full hpoint hopenZ hopenSucc hbox
      hleadingCall hfullCall hleadingCan hfullCan hleadingModel hfullModel
  refine ⟨out,?_,houtCanonical,?_⟩
  · rw [run,hselectors]
    simp only [bind_tc_ok]
    rw [AspisR1SelectedMaskProbe.evaluator_qname_eq_factored]
    exact hout
  · intro g
    simpa only [model,AspisR1.PoseidonClosure2ArrayExact.cell4,Decode,pointSelector,lane,
      AspisR1.PoseidonCandidateProjectedScalarResidualFromBoxed.Decode,
      AspisR1.PoseidonCandidateProjectedScalarResidualFromBoxed.pointSelector,
      AspisR1.PoseidonSamePointResidualModel.iBasis,AspisR1.PoseidonSamePointResidualModel.uBasis,
      AspisR1.PoseidonSamePointResidualModel.lane,
      AspisR1.PoseidonResidualPacking.lane,AspisR1.PoseidonExternalPackedModel.lane] using hmodel g

#print axioms callable
end R1Z.ProverCommitPoseidonCallable55
