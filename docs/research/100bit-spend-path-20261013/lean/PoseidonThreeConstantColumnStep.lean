import PoseidonThreeConstantColumnsSource
import PoseidonThreeConstantCell
import OccupancyRangeTraversal

/-! Bind each interpolated constant cell to actual weight and column reads,
then to the actual output-array update. -/
set_option autoImplicit false
namespace AspisR1.PoseidonThreeConstantColumnStep
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
open AspisR1.PoseidonFullRoundCellStep
abbrev Weights := Array QM 3#usize

def CanonicalWeights (weights : Weights) : Prop := ∀ i : Fin 3, Canonical (cell weights i)
def model (weights : Weights) (c0 c1 c2 : Constants) (lane : Fin 16) : Exact :=
  Decode (cell weights (0 : Fin 3)) * ((cell c0 lane).val : Exact) +
  Decode (cell weights (1 : Fin 3)) * ((cell c1 lane).val : Exact) +
  Decode (cell weights (2 : Fin 3)) * ((cell c2 lane).val : Exact)

def sourceStep (weights : Weights) (c0 c1 c2 : Constants) (out : State) (lane : Usize) : Result State := do
  let w0 ← Array.index_usize weights 0#usize
  let w1 ← Array.index_usize weights 1#usize
  let w2 ← Array.index_usize weights 2#usize
  let k0 ← Array.index_usize c0 lane
  let k1 ← Array.index_usize c1 lane
  let k2 ← Array.index_usize c2 lane
  let value ← AspisR1.PoseidonThreeConstantCell.source w0 w1 w2 k0 k1 k2
  Array.update out lane value

theorem sourceStep_success (weights : Weights) (c0 c1 c2 : Constants) (out : State)
    (lane : Usize) (hlane : lane.val < 16) (hw : CanonicalWeights weights)
    (hc0 : CanonicalConstants c0) (hc1 : CanonicalConstants c1) (hc2 : CanonicalConstants c2)
    (hout : CanonicalState out) :
    ∃ value : QM, sourceStep weights c0 c1 c2 out lane = .ok (out.set lane value) ∧
      CanonicalState (out.set lane value) ∧ ∀ j : Fin 16,
      Decode (cell (out.set lane value) j) =
        if j.val = lane.val then model weights c0 c1 c2 ⟨lane.val,hlane⟩ else Decode (cell out j) := by
  let index : Fin 16 := ⟨lane.val,hlane⟩
  let w0 := cell weights (0 : Fin 3)
  let w1 := cell weights (1 : Fin 3)
  let w2 := cell weights (2 : Fin 3)
  let k0 := cell c0 index
  let k1 := cell c1 index
  let k2 := cell c2 index
  have hr0 : Array.index_usize weights 0#usize = .ok w0 := by
    have hread := AspisR1.ExtractedMaskHornerStep.array_index_usize_ok weights 0#usize (by decide)
    change Array.index_usize weights 0#usize = .ok (weights.val[0]'(by simpa [weights.property] using (by decide : 0 < 3))) at hread
    change Array.index_usize weights 0#usize = .ok (weights.val[0]'(by simpa [weights.property] using (by decide : 0 < 3)))
    exact hread
  have hr1 : Array.index_usize weights 1#usize = .ok w1 := by
    have hread := AspisR1.ExtractedMaskHornerStep.array_index_usize_ok weights 1#usize (by decide)
    change Array.index_usize weights 1#usize = .ok (weights.val[1]'(by simpa [weights.property] using (by decide : 1 < 3))) at hread
    change Array.index_usize weights 1#usize = .ok (weights.val[1]'(by simpa [weights.property] using (by decide : 1 < 3)))
    exact hread
  have hr2 : Array.index_usize weights 2#usize = .ok w2 := by
    have hread := AspisR1.ExtractedMaskHornerStep.array_index_usize_ok weights 2#usize (by decide)
    change Array.index_usize weights 2#usize = .ok (weights.val[2]'(by simpa [weights.property] using (by decide : 2 < 3))) at hread
    change Array.index_usize weights 2#usize = .ok (weights.val[2]'(by simpa [weights.property] using (by decide : 2 < 3)))
    exact hread
  have hb : lane.val < (16#usize).val := by simpa using hlane
  have hc0read : Array.index_usize c0 lane = .ok k0 := by
    simpa only [k0,index,cell] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok c0 lane hb
  have hc1read : Array.index_usize c1 lane = .ok k1 := by
    simpa only [k1,index,cell] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok c1 lane hb
  have hc2read : Array.index_usize c2 lane = .ok k2 := by
    simpa only [k2,index,cell] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok c2 lane hb
  obtain ⟨value,hvalue,hcan,hmodel⟩ := AspisR1.PoseidonThreeConstantCell.source_success
    w0 w1 w2 k0 k1 k2 (hw 0) (hw 1) (hw 2) (hc0 index) (hc1 index) (hc2 index)
  change Decode value = model weights c0 c1 c2 index at hmodel
  obtain ⟨updated,hupdate,hset⟩ := WP.spec_imp_exists
    (Array.update_spec out lane value (by simpa [out.property] using hb))
  have hwrite : Array.update out lane value = .ok (out.set lane value) := by rw [hupdate,hset]
  refine ⟨value,?_,set_canonical out lane value hout hcan,?_⟩
  · simp only [sourceStep,hr0,hr1,hr2,hc0read,hc1read,hc2read,hvalue,hwrite,bind_tc_ok]
  · intro j
    rw [cell_set]
    by_cases hj : j.val = lane.val
    · simp only [if_pos hj]
      exact hmodel
    · simp only [if_neg hj]

theorem generated_loop_step (weights : Weights) (c0 c1 c2 : Constants) (out : State) (lane : Usize) :
    state_only_poseidon.interpolate_three_constant_columns_loop weights c0 c1 c2 out lane =
      (if lane < poseidon2.POSEIDON2_WIDTH then do
        let nextState ← sourceStep weights c0 c1 c2 out lane
        let lane1 ← lane + 1#usize
        state_only_poseidon.interpolate_three_constant_columns_loop weights c0 c1 c2 nextState lane1
      else .ok out) := by
  rw [state_only_poseidon.interpolate_three_constant_columns_loop.eq_def]
  simp only [sourceStep,AspisR1.PoseidonThreeConstantCell.source,bind_assoc_eq]
  rfl

#print axioms sourceStep_success
#print axioms generated_loop_step
end AspisR1.PoseidonThreeConstantColumnStep
