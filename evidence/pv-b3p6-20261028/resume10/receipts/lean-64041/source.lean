import PV_B3P_ValueRead913227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_13 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q168 ← reference_terminal.read227 range_input 30#usize
  let q169 ← aspis_core.field.QM31.mul range_selector q168
  let range64 ← Array.update range_input 30#usize q169
  let q170 ← reference_terminal.read227 range64 31#usize
  let q171 ← aspis_core.field.QM31.mul range_selector q170
  let range65 ← Array.update range64 31#usize q171
  let q172 ← reference_terminal.read227 range65 32#usize
  let q173 ← aspis_core.field.QM31.mul range_selector q172
  let range66 ← Array.update range65 32#usize q173
  f range66) = (value_owned_stage9_13 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_13 value_read_context9_13
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_13
end PV_B3P_Binding10227
