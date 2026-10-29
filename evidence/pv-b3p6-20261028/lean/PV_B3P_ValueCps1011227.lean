import PV_B3P_ValueRead911227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_11 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q144 ← reference_terminal.read227 range_input 18#usize
  let q145 ← aspis_core.field.QM31.mul range_selector q144
  let range52 ← Array.update range_input 18#usize q145
  let q146 ← reference_terminal.read227 range52 19#usize
  let q147 ← aspis_core.field.QM31.mul range_selector q146
  let range53 ← Array.update range52 19#usize q147
  let q148 ← reference_terminal.read227 range53 20#usize
  let q149 ← aspis_core.field.QM31.mul range_selector q148
  let range54 ← Array.update range53 20#usize q149
  let q150 ← reference_terminal.read227 range54 21#usize
  let q151 ← aspis_core.field.QM31.mul range_selector q150
  let range55 ← Array.update range54 21#usize q151
  let q152 ← reference_terminal.read227 range55 22#usize
  let q153 ← aspis_core.field.QM31.mul range_selector q152
  let range56 ← Array.update range55 22#usize q153
  let q154 ← reference_terminal.read227 range56 23#usize
  let q155 ← aspis_core.field.QM31.mul range_selector q154
  let range57 ← Array.update range56 23#usize q155
  f range57) = (value_owned_stage9_11 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_11 value_read_context9_11
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_11
end PV_B3P_Binding10227
