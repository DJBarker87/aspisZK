import AspisR1.PoseidonCallable53
import PoseidonCandidateProjectedEvaluatorSourceV12
/-! Transfer the already proved part-53 callable to the literal evaluator
QName source cut. Native Rust correspondence remains separate. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPoseidonCallable55
open Aeneas Aeneas.Std Result AspisR1SelectedMaskProbe
open AspisR1.PoseidonSamePointResidualModel
abbrev QM := field.QM31
abbrev Exact := AspisV8R15.ExactTowerBase.QM31Exact
abbrev Decode := AspisR1.ExtractedMaskQM31Exact.decode
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
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

theorem source_same (o : Openings) (selectors : pool_v1.pair_forest_copy_terminal.Selectors) :
    run o selectors=AspisR1.PoseidonCallable53.source o selectors := by
  simp only [run,AspisR1.PoseidonCallable53.source,AspisR1SelectedMaskProbe.evaluator_qname_eq_factored]

theorem model_same (p : Array QM 10#usize) (o : Openings)
    (selectors : pool_v1.pair_forest_copy_terminal.Selectors) (g : Fin 4) :
    model p o g=AspisR1.PoseidonCallable53.model p o selectors g := rfl

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
  obtain ⟨out,hout,hcan,hmodel⟩ := AspisR1.PoseidonCallable53.source_success
    openings point selectorInput hpoint hopenZ hopenSucc hopenXor hbox
  refine ⟨out,?_,hcan,?_⟩
  · rw [source_same];exact hout
  · intro g
    rw [model_same point openings selectorInput g]
    simpa only [AspisR1.PoseidonCallable53.cell,AspisR1.PoseidonClosure2ArrayExact.cell4] using hmodel g

#print axioms source_same
#print axioms model_same
#print axioms callable
end R1Z.ProverCommitPoseidonCallable55
