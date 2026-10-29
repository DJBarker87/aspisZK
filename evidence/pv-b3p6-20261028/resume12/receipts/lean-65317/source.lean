import PV_B3P_LeadingCell122227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 Result
set_option autoImplicit false

def leading_tail12_1 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (state : LeadingState12) : Result (Array aspis_core.field.QM31 4#usize) := do
  let q3 ← Array.index_usize state 1#usize
  let q4 ← Array.index_usize openings.xor12_z 1#usize
  let q5 ← aspis_core.field.QM31.add q3 q4
  let state1 ← Array.update state 1#usize q5
  let q6 ← Array.index_usize state1 2#usize
  let q7 ← Array.index_usize openings.xor12_z 2#usize
  let q8 ← aspis_core.field.QM31.add q6 q7
  let state2 ← Array.update state1 2#usize q8
  let q9 ← Array.index_usize state2 3#usize
  let q10 ← Array.index_usize openings.xor12_z 3#usize
  let q11 ← aspis_core.field.QM31.add q9 q10
  let state3 ← Array.update state2 3#usize q11
  let q12 ← Array.index_usize state3 4#usize
  let q13 ← Array.index_usize openings.xor12_z 4#usize
  let q14 ← aspis_core.field.QM31.add q12 q13
  let state4 ← Array.update state3 4#usize q14
  let q15 ← Array.index_usize state4 5#usize
  let q16 ← Array.index_usize openings.xor12_z 5#usize
  let q17 ← aspis_core.field.QM31.add q15 q16
  let state5 ← Array.update state4 5#usize q17
  let q18 ← Array.index_usize state5 6#usize
  let q19 ← Array.index_usize openings.xor12_z 6#usize
  let q20 ← aspis_core.field.QM31.add q18 q19
  let state6 ← Array.update state5 6#usize q20
  let q21 ← Array.index_usize state6 7#usize
  let q22 ← Array.index_usize openings.xor12_z 7#usize
  let q23 ← aspis_core.field.QM31.add q21 q22
  let state7 ← Array.update state6 7#usize q23
  let state8 ← reference_poseidon.external_linear_lazy state7
  let a ← Array.index_usize reference_poseidon.EXTERNAL_INITIAL 0#usize
  let a1 ← reference_poseidon.full_round_m31_constants state8 a
  let a2 ← Array.index_usize reference_poseidon.EXTERNAL_INITIAL 1#usize
  reference_poseidon.full_round_m31_constants_packed a1 a2
attribute [local irreducible] aspis_core.field.QM31.add Array.index_usize Array.update leading_step12 leading_finish12 leading_tail12_2
theorem leading_cell12_1 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (state : LeadingState12) :
    leading_tail12_1 openings state =
      (leading_step12 openings.xor12_z state 1#usize >>= leading_tail12_2 openings) := by
  unfold leading_tail12_1
  conv_rhs => simp only [leading_step12,PV_B3P_Ordered227.bind_assoc]
  apply PV_B3P_Binding9227.bind_equal9
  intro v0
  apply PV_B3P_Binding9227.bind_equal9
  intro v1
  apply PV_B3P_Binding9227.bind_equal9
  intro v2
  apply PV_B3P_Binding9227.bind_equal9
  intro next
  unfold leading_tail12_2
  rfl
theorem leading_fold12_1 (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) (state : LeadingState12) :
    leading_tail12_1 openings state =
      (PV_B3P_Ordered227.fold (leading_step12 openings.xor12_z)
        [1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize] state >>= leading_finish12) := by
  rw [leading_cell12_1]
  simp only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc]
  apply congrArg (fun f => leading_step12 openings.xor12_z state 1#usize >>= f)
  funext next
  simpa only [PV_B3P_Ordered227.fold,PV_B3P_Ordered227.bind_assoc,bind_tc_ok] using leading_fold12_2 openings next
#print axioms leading_cell12_1
#print axioms leading_fold12_1
end PV_B3P_Binding12227
