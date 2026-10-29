import PV_B3P_ValueRead910227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_10 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q132 ← reference_terminal.read227 range_input 12#usize
  let q133 ← aspis_core.field.QM31.mul range_selector q132
  let range46 ← Array.update range_input 12#usize q133
  let q134 ← reference_terminal.read227 range46 13#usize
  let q135 ← aspis_core.field.QM31.mul range_selector q134
  let range47 ← Array.update range46 13#usize q135
  let q136 ← reference_terminal.read227 range47 14#usize
  let q137 ← aspis_core.field.QM31.mul range_selector q136
  let range48 ← Array.update range47 14#usize q137
  let q138 ← reference_terminal.read227 range48 15#usize
  let q139 ← aspis_core.field.QM31.mul range_selector q138
  let range49 ← Array.update range48 15#usize q139
  let q140 ← reference_terminal.read227 range49 16#usize
  let q141 ← aspis_core.field.QM31.mul range_selector q140
  let range50 ← Array.update range49 16#usize q141
  let q142 ← reference_terminal.read227 range50 17#usize
  let q143 ← aspis_core.field.QM31.mul range_selector q142
  let range51 ← Array.update range50 17#usize q143
  f range51) = (value_owned_stage9_10 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_10 value_read_context9_10
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_10
end PV_B3P_Binding10227
