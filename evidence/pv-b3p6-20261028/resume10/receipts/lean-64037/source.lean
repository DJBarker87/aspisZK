import PV_B3P_ValueRead909227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_09 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q120 ← reference_terminal.read227 range_input 6#usize
  let q121 ← aspis_core.field.QM31.mul range_selector q120
  let range40 ← Array.update range_input 6#usize q121
  let q122 ← reference_terminal.read227 range40 7#usize
  let q123 ← aspis_core.field.QM31.mul range_selector q122
  let range41 ← Array.update range40 7#usize q123
  let q124 ← reference_terminal.read227 range41 8#usize
  let q125 ← aspis_core.field.QM31.mul range_selector q124
  let range42 ← Array.update range41 8#usize q125
  let q126 ← reference_terminal.read227 range42 9#usize
  let q127 ← aspis_core.field.QM31.mul range_selector q126
  let range43 ← Array.update range42 9#usize q127
  let q128 ← reference_terminal.read227 range43 10#usize
  let q129 ← aspis_core.field.QM31.mul range_selector q128
  let range44 ← Array.update range43 10#usize q129
  let q130 ← reference_terminal.read227 range44 11#usize
  let q131 ← aspis_core.field.QM31.mul range_selector q130
  let range45 ← Array.update range44 11#usize q131
  f range45) = (value_owned_stage9_09 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_09 value_read_context9_09
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_09
end PV_B3P_Binding10227
