import PV_B3P_ValueRead902227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_02 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q23 ← reference_terminal.read227 openings.z 5#usize
  let q24 ← aspis_core.field.QM31.square q23
  let q25 ← aspis_core.field.QM31.sub q24 q23
  let range6 ← Array.update range_input 5#usize q25
  let q26 ← reference_terminal.read227 openings.z 6#usize
  let q27 ← aspis_core.field.QM31.square q26
  let q28 ← aspis_core.field.QM31.sub q27 q26
  let range7 ← Array.update range6 6#usize q28
  let q29 ← reference_terminal.read227 openings.z 7#usize
  let q30 ← aspis_core.field.QM31.square q29
  let q31 ← aspis_core.field.QM31.sub q30 q29
  let range8 ← Array.update range7 7#usize q31
  let q32 ← reference_terminal.read227 openings.z 8#usize
  let q33 ← aspis_core.field.QM31.square q32
  let q34 ← aspis_core.field.QM31.sub q33 q32
  let range9 ← Array.update range8 8#usize q34
  let q35 ← reference_terminal.read227 openings.z 9#usize
  let q36 ← aspis_core.field.QM31.square q35
  let q37 ← aspis_core.field.QM31.sub q36 q35
  let range10 ← Array.update range9 9#usize q37
  f range10) = (value_owned_stage9_02 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_02 value_read_context9_02
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_02
end PV_B3P_Binding10227
