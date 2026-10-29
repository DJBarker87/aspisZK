import PV_B3P_ValueRead908227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_08 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q108 ← reference_terminal.read227 range_input 0#usize
  let q109 ← aspis_core.field.QM31.mul range_selector q108
  let range34 ← Array.update range_input 0#usize q109
  let q110 ← reference_terminal.read227 range34 1#usize
  let q111 ← aspis_core.field.QM31.mul range_selector q110
  let range35 ← Array.update range34 1#usize q111
  let q112 ← reference_terminal.read227 range35 2#usize
  let q113 ← aspis_core.field.QM31.mul range_selector q112
  let range36 ← Array.update range35 2#usize q113
  let q114 ← reference_terminal.read227 range36 3#usize
  let q115 ← aspis_core.field.QM31.mul range_selector q114
  let range37 ← Array.update range36 3#usize q115
  let q116 ← reference_terminal.read227 range37 4#usize
  let q117 ← aspis_core.field.QM31.mul range_selector q116
  let range38 ← Array.update range37 4#usize q117
  let q118 ← reference_terminal.read227 range38 5#usize
  let q119 ← aspis_core.field.QM31.mul range_selector q118
  let range39 ← Array.update range38 5#usize q119
  f range39) = (value_owned_stage9_08 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_08 value_read_context9_08
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_08
end PV_B3P_Binding10227
