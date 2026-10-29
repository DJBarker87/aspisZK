import PV_B3P_AbsorptionCell15_02227
namespace PV_B3P_Native15227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 Result
set_option autoImplicit false

def absorption_tail15_01 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) (state : Array aspis_core.field.QM31 16#usize) : Result (Array aspis_core.field.QM31 16#usize) := do
  let q2 ← reference_terminal.read227 openings 1#usize
  let q3 ←
    reference_terminal.absorption_lane227 1#usize low fixed chunk_two
      chunk_eight nodes q2
  let output2 ← Array.update state 1#usize q3
  let q4 ← reference_terminal.read227 openings 2#usize
  let q5 ←
    reference_terminal.absorption_lane227 2#usize low fixed chunk_two
      chunk_eight nodes q4
  let output3 ← Array.update output2 2#usize q5
  let q6 ← reference_terminal.read227 openings 3#usize
  let q7 ←
    reference_terminal.absorption_lane227 3#usize low fixed chunk_two
      chunk_eight nodes q6
  let output4 ← Array.update output3 3#usize q7
  let q8 ← reference_terminal.read227 openings 4#usize
  let q9 ←
    reference_terminal.absorption_lane227 4#usize low fixed chunk_two
      chunk_eight nodes q8
  let output5 ← Array.update output4 4#usize q9
  let q10 ← reference_terminal.read227 openings 5#usize
  let q11 ←
    reference_terminal.absorption_lane227 5#usize low fixed chunk_two
      chunk_eight nodes q10
  let output6 ← Array.update output5 5#usize q11
  let q12 ← reference_terminal.read227 openings 6#usize
  let q13 ←
    reference_terminal.absorption_lane227 6#usize low fixed chunk_two
      chunk_eight nodes q12
  let output7 ← Array.update output6 6#usize q13
  let q14 ← reference_terminal.read227 openings 7#usize
  let q15 ←
    reference_terminal.absorption_lane227 7#usize low fixed chunk_two
      chunk_eight nodes q14
  let output8 ← Array.update output7 7#usize q15
  let q16 ← reference_terminal.read227 openings 8#usize
  let q17 ←
    reference_terminal.absorption_lane227 8#usize low fixed chunk_two
      chunk_eight nodes q16
  let output9 ← Array.update output8 8#usize q17
  let q18 ← reference_terminal.read227 openings 9#usize
  let q19 ←
    reference_terminal.absorption_lane227 9#usize low fixed chunk_two
      chunk_eight nodes q18
  let output10 ← Array.update output9 9#usize q19
  let q20 ← reference_terminal.read227 openings 10#usize
  let q21 ←
    reference_terminal.absorption_lane227 10#usize low fixed chunk_two
      chunk_eight nodes q20
  let output11 ← Array.update output10 10#usize q21
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
attribute [local irreducible] Array.index_usize Array.update reference_terminal.read227 reference_terminal.absorption_lane227 reference_poseidon.interpolate_column227 absorption_step15 absorption_tail15_02
theorem absorption_cell15_01 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) (state : Array aspis_core.field.QM31 16#usize) :
    absorption_tail15_01 low fixed chunk_two chunk_eight nodes openings state =
      (absorption_step15 low fixed chunk_two chunk_eight nodes openings state 1#usize >>= absorption_tail15_02 low fixed chunk_two chunk_eight nodes openings) := by
  unfold absorption_tail15_01
  conv_rhs => simp only [absorption_step15,PV_B3P_Ordered227.bind_assoc]
  apply bind_equal9
  intro v0
  apply bind_equal9
  intro v1
  apply bind_equal9
  intro next
  unfold absorption_tail15_02
  rfl
theorem absorption_fold15_01 (low fixed chunk_two chunk_eight nodes : aspis_core.field.QM31) (openings : Array aspis_core.field.QM31 16#usize) (state : Array aspis_core.field.QM31 16#usize) :
    absorption_tail15_01 low fixed chunk_two chunk_eight nodes openings state =
      PV_B3P_Ordered227.fold (absorption_step15 low fixed chunk_two chunk_eight nodes openings) [1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize,8#usize,9#usize,10#usize,11#usize,12#usize,13#usize,14#usize,15#usize] state := by
  rw [absorption_cell15_01]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
  apply congrArg (fun k => absorption_step15 low fixed chunk_two chunk_eight nodes openings state 1#usize >>= k)
  funext next
  exact absorption_fold15_02 low fixed chunk_two chunk_eight nodes openings next
#print axioms absorption_cell15_01
#print axioms absorption_fold15_01
end PV_B3P_Native15227
