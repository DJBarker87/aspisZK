import PreweightedClosureSuccess
import SelectedClaimGatherSlice
import ExtractedMaskConstants
import SelectorExpansionCorrectness

/-! The actual stable from_fn-copy helper constructs the exact zero-padded
four-cell interval selected by add_preweighted. Canonicality is inherited from
input lanes, including groups straddling either boundary. -/
set_option autoImplicit false
namespace AspisR1.PreweightedLaneArray
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.PreweightedClosureSuccess

abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM

theorem selectedCell_canonical {N : Usize}
    (values : Array QM N) (start group slot : Nat)
    (hvalues : AspisR1.SelectorExpansionCorrectness.canonicalArray values) :
    Canonical (selectedCell values start group slot) := by
  unfold selectedCell
  split
  · rename_i h
    have hidx : 4 * group + slot - start < N.val := by omega
    unfold sourceCell
    rw [dif_pos hidx]
    exact hvalues ⟨4 * group + slot - start, by simpa [values.property] using hidx⟩
  · exact AspisR1.ExtractedMaskConstants.zero_canonical

theorem lane_array_success {N : Usize}
    (values : Array QM N) (group start : Usize)
    (hgroup : group.val < 24) (hinterval : start.val + N.val ≤ 96)
    (hvalues : AspisR1.SelectorExpansionCorrectness.canonicalArray values) :
    ∃ lanes : Array QM 4#usize,
      array_from_fn_copy 4#usize field.QM31.Insts.CoreMarkerCopy
        (AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N)
        field.QM31.ZERO (group, start, values) = .ok lanes ∧
      AspisR1.SelectorExpansionCorrectness.canonicalArray lanes ∧
      ∀ j : Fin 4,
        lanes.val[j.val]'(by simpa [lanes.property] using j.isLt) =
          selectedCell values start.val group.val j.val := by
  let inst := AspisR1PreweightedCandidate.pool_v1.pair_forest_semantic_terminal.add_preweighted.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31 N
  let value : Nat → QM := selectedCell values start.val group.val
  have hstable : ∀ i : Usize, i.val < (4#usize).val →
      inst.call_mut (group, start, values) i =
        .ok (value i.val, (group, start, values)) := by
    intro i hi
    exact call_mut_success values group start i hgroup (by simpa using hi) hinterval
  obtain ⟨lanes, hrun, hcells⟩ := array_from_fn_copy_stable
    4#usize field.QM31.Insts.CoreMarkerCopy inst field.QM31.ZERO
    (group, start, values) value hstable
  refine ⟨lanes, hrun, ?_, ?_⟩
  · intro j
    have hj : j.val < (4#usize).val := by simpa [lanes.property] using j.isLt
    have heq := hcells j.val hj
    rw [heq]
    exact selectedCell_canonical values start.val group.val j.val hvalues
  · intro j
    exact hcells j.val (by simpa using j.isLt)

#print axioms selectedCell_canonical
#print axioms lane_array_success
end AspisR1.PreweightedLaneArray
