import PV_B3P_ValueRead901227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_01 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q8 ← reference_terminal.read227 openings.z 0#usize
  let q9 ← aspis_core.field.QM31.square q8
  let q10 ← aspis_core.field.QM31.sub q9 q8
  let range1 ← Array.update range_input 0#usize q10
  let q11 ← reference_terminal.read227 openings.z 1#usize
  let q12 ← aspis_core.field.QM31.square q11
  let q13 ← aspis_core.field.QM31.sub q12 q11
  let range2 ← Array.update range1 1#usize q13
  let q14 ← reference_terminal.read227 openings.z 2#usize
  let q15 ← aspis_core.field.QM31.square q14
  let q16 ← aspis_core.field.QM31.sub q15 q14
  let range3 ← Array.update range2 2#usize q16
  let q17 ← reference_terminal.read227 openings.z 3#usize
  let q18 ← aspis_core.field.QM31.square q17
  let q19 ← aspis_core.field.QM31.sub q18 q17
  let range4 ← Array.update range3 3#usize q19
  let q20 ← reference_terminal.read227 openings.z 4#usize
  let q21 ← aspis_core.field.QM31.square q20
  let q22 ← aspis_core.field.QM31.sub q21 q20
  let range5 ← Array.update range4 4#usize q22
  f range5) = (value_owned_stage9_01 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_01 value_read_context9_01
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_01
end PV_B3P_Binding10227
