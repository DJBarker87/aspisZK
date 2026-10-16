import PathLaneSourcePrefix
import PathLaneSourceLoop
import PathLaneLoopMeaning

/-! Complete actual literal path residual construction. Input canonicality
suffices for all checked calls and every returned residual equation. -/
set_option autoImplicit false
namespace AspisR1.PathLaneLiteralExecution
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PathLaneSourceStep
open AspisR1.PathLaneSourceLoop
open AspisR1.PathLaneSourcePrefix
open AspisR1.PreweightedGroupUpdate
open AspisR1.ExtractedMaskQM31Exact

abbrev Literal := AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal

theorem literal_execution
    (selector : QM) (openings : Openings)
    (hs : Canonical selector) (hz : CanonicalArray openings.z)
    (hsucc : CanonicalArray openings.succ_z) :
    ∃ out, Literal selector openings = .ok out ∧ CanonicalArray out ∧
      decode (cell out ⟨0, by scalar_tac⟩) = decode selector *
        (decode (cell openings.z bitIndex) * (decode (cell openings.z bitIndex) - 1)) ∧
      (∀ i : Fin 8, decode (cell out ⟨1 + i.val, by change 1 + i.val < 17; omega⟩) =
        left selector (cell openings.z bitIndex) openings.z openings.succ_z i.val) ∧
      (∀ i : Fin 8, decode (cell out ⟨9 + i.val, by change 9 + i.val < 17; omega⟩) =
        right selector (cell openings.z bitIndex) openings.z openings.succ_z i.val) := by
  obtain ⟨bit, path, hprefix, hbit, hcbit, hcpath, hprefixValues⟩ :=
    prefix_success selector openings hs hz
  let iter : Range :=
    { start := 0#usize, «end» := AspisR1PathLaneCandidate.poseidon2.DIGEST_ELEMS }
  obtain ⟨out, hloop, hcanonical, hmodel⟩ :=
    loop_model 8 iter selector openings.z openings.succ_z bit path
      (by simp only [iter, AspisR1PathLaneCandidate.poseidon2.DIGEST_ELEMS]; rfl)
      (by simp only [iter]; rfl) hs hcbit hz hsucc hcpath
  have hmodel' : decoded out =
      applySteps selector bit openings.z openings.succ_z 8 0 (decoded path) := by
    have hzeroVal : (0#usize).val = 0 := by scalar_tac
    simpa only [iter, hzeroVal] using hmodel
  obtain ⟨hzero, hleft, hright⟩ := AspisR1.PathLaneLoopMeaning.applySteps_from_zero
    selector bit openings.z openings.succ_z (decoded path)
  refine ⟨out, ?_, hcanonical, ?_, ?_, ?_⟩
  · change AspisR1PathLaneCandidate.pool_v1.pair_forest_semantic_terminal.path_lanes_literal
      selector openings = .ok out
    rw [generated_wrapper_eq]
    simp only [hprefix, bind_tc_ok]
    exact hloop
  · have hprefixZero := hprefixValues 0
    simp only [Fin.val_zero, if_pos rfl] at hprefixZero
    have hzero' := congrFun hmodel' 0
    rw [hzero] at hzero'
    change decode (cell out (0 : Fin 17)) = decode (cell path (0 : Fin 17)) at hzero'
    rw [hprefixZero, hbit] at hzero'
    exact hzero'
  · intro i
    have hi := congrFun hmodel' ⟨1 + i.val, by change 1 + i.val < 17; omega⟩
    rw [hleft i, hbit] at hi
    exact hi
  · intro i
    have hi := congrFun hmodel' ⟨9 + i.val, by change 9 + i.val < 17; omega⟩
    rw [hright i, hbit] at hi
    exact hi

#print axioms literal_execution
end
end AspisR1.PathLaneLiteralExecution
