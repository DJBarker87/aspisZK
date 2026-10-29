import PV_B3P_PathCell15_0227
import PV_B3P_NativeLeading15227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def native_path15 (path_selector : aspis_core.field.QM31) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) : Result PathState15 := do
  let bit ← Array.index_usize openings.z 0#usize
  let path := Array.repeat 17#usize aspis_core.field.QM31.ZERO
  let q ← aspis_core.field.QM31.sub bit aspis_core.field.QM31.ONE
  let q1 ← aspis_core.field.QM31.mul bit q
  let q2 ← aspis_core.field.QM31.mul path_selector q1
  let path1 ← Array.update path 0#usize q2
  range_loop13 (path_step15 path_selector openings bit) 0#usize 8#usize path1
attribute [local irreducible] Array.index_usize Array.update aspis_core.field.QM31.sub aspis_core.field.QM31.mul path_step15 path_tail15_0
theorem native_path_binding15 (path_selector : aspis_core.field.QM31) (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    native_path15 path_selector openings = reference_terminal.path_lanes_literal path_selector openings := by
  unfold native_path15 reference_terminal.path_lanes_literal
  apply bind_equal9
  intro p0
  apply bind_equal9
  intro p1
  apply bind_equal9
  intro p2
  apply bind_equal9
  intro p3
  apply bind_equal9
  intro p4
  obtain ⟨minus,hsub⟩ := PV_B3P_Success227.qsub aspis_core.field.QM31.ONE p0
  obtain ⟨right,hmul⟩ := PV_B3P_Success227.qmul path_selector p0
  rw [range_as_fold13 _ 0#usize 8#usize 8 _ (by rfl),leading_indices15]
  exact (path_fold15_0 path_selector openings p0 minus right p4 hsub hmul).symm
#print axioms native_path_binding15
end PV_B3P_Native15227
