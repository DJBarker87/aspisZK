import PV_B3P_AbsorptionCell15_11227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def absorption_tail15_10 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) (state : Array aspis_core.field.QM31 16#usize) : Result (Array aspis_core.field.QM31 16#usize) := do
  let q20 ← reference_terminal.read227 openings 10#usize
  let q21 ←
    reference_terminal.absorption_lane227 10#usize low fixed chunk_two
      chunk_eight nodes q20
  let output11 ← Array.update state 10#usize q21
  let q22 ← reference_terminal.read227 openings 11#usize
  let q23 ←
    reference_terminal.absorption_lane227 11#usize low fixed chunk_two
      chunk_eight nodes q22
  let output12 ← Array.update output11 11#usize q23
  let q24 ← reference_terminal.read227 openings 12#usize
  let q25 ←
    reference_terminal.absorption_lane227 12#usize low fixed chunk_two
      chunk_eight nodes q24
  let output13 ← Array.update output12 12#usize q25
  let q26 ← reference_terminal.read227 openings 13#usize
  let q27 ←
    reference_terminal.absorption_lane227 13#usize low fixed chunk_two
      chunk_eight nodes q26
  let output14 ← Array.update output13 13#usize q27
  let q28 ← reference_terminal.read227 openings 14#usize
  let q29 ←
    reference_terminal.absorption_lane227 14#usize low fixed chunk_two
      chunk_eight nodes q28
  let output15 ← Array.update output14 14#usize q29
  let q30 ← reference_terminal.read227 openings 15#usize
  let q31 ←
    reference_terminal.absorption_lane227 15#usize low fixed chunk_two
      chunk_eight nodes q30
  Array.update output15 15#usize q31
attribute [local irreducible] Array.index_usize Array.update reference_terminal.read227 reference_terminal.absorption_lane227 reference_poseidon.interpolate_column227 absorption_step15 absorption_tail15_11
theorem absorption_cell15_10 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) (state : Array aspis_core.field.QM31 16#usize) :
    absorption_tail15_10 low fixed chunk_two chunk_eight nodes openings state =
      (absorption_step15 low fixed chunk_two chunk_eight nodes openings state 10#usize >>= absorption_tail15_11 low fixed chunk_two chunk_eight nodes openings) := by
  unfold absorption_tail15_10
  conv_rhs => simp only [absorption_step15,PV_B3P_Ordered227.bind_assoc]
  apply bind_equal9
  intro v0
  apply bind_equal9
  intro v1
  apply bind_equal9
  intro next
  unfold absorption_tail15_11
  rfl
theorem absorption_fold15_10 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) (state : Array aspis_core.field.QM31 16#usize) :
    absorption_tail15_10 low fixed chunk_two chunk_eight nodes openings state =
      PV_B3P_Ordered227.fold (absorption_step15 low fixed chunk_two chunk_eight nodes openings) [10#usize,11#usize,12#usize,13#usize,14#usize,15#usize] state := by
  rw [absorption_cell15_10]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
  apply congrArg (fun k => absorption_step15 low fixed chunk_two chunk_eight nodes openings state 10#usize >>= k)
  funext next
  exact absorption_fold15_11 low fixed chunk_two chunk_eight nodes openings next
#print axioms absorption_cell15_10
#print axioms absorption_fold15_10
end PV_B3P_Native15227
