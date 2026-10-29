import PV_B3P_ValueRead912227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_12 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q156 ← reference_terminal.read227 range_input 24#usize
  let q157 ← aspis_core.field.QM31.mul range_selector q156
  let range58 ← Array.update range_input 24#usize q157
  let q158 ← reference_terminal.read227 range58 25#usize
  let q159 ← aspis_core.field.QM31.mul range_selector q158
  let range59 ← Array.update range58 25#usize q159
  let q160 ← reference_terminal.read227 range59 26#usize
  let q161 ← aspis_core.field.QM31.mul range_selector q160
  let range60 ← Array.update range59 26#usize q161
  let q162 ← reference_terminal.read227 range60 27#usize
  let q163 ← aspis_core.field.QM31.mul range_selector q162
  let range61 ← Array.update range60 27#usize q163
  let q164 ← reference_terminal.read227 range61 28#usize
  let q165 ← aspis_core.field.QM31.mul range_selector q164
  let range62 ← Array.update range61 28#usize q165
  let q166 ← reference_terminal.read227 range62 29#usize
  let q167 ← aspis_core.field.QM31.mul range_selector q166
  let range63 ← Array.update range62 29#usize q167
  f range63) = (value_owned_stage9_12 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_12 value_read_context9_12
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_12
end PV_B3P_Binding10227
