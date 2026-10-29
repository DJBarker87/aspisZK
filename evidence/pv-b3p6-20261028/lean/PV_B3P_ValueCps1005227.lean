import PV_B3P_ValueRead905227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_05 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q68 ← reference_terminal.read227 openings.xor12_z 0#usize
  let q69 ← aspis_core.field.QM31.square q68
  let q70 ← aspis_core.field.QM31.sub q69 q68
  let i15 ← lift (Std.Usize.wrapping_add 20#usize 0#usize)
  let range21 ← Array.update range_input i15 q70
  let q71 ← reference_terminal.read227 openings.xor12_z 1#usize
  let q72 ← aspis_core.field.QM31.square q71
  let q73 ← aspis_core.field.QM31.sub q72 q71
  let i16 ← lift (Std.Usize.wrapping_add 20#usize 1#usize)
  let range22 ← Array.update range21 i16 q73
  let q74 ← reference_terminal.read227 openings.xor12_z 2#usize
  let q75 ← aspis_core.field.QM31.square q74
  let q76 ← aspis_core.field.QM31.sub q75 q74
  let i17 ← lift (Std.Usize.wrapping_add 20#usize 2#usize)
  let range23 ← Array.update range22 i17 q76
  let q77 ← reference_terminal.read227 openings.xor12_z 3#usize
  let q78 ← aspis_core.field.QM31.square q77
  let q79 ← aspis_core.field.QM31.sub q78 q77
  let i18 ← lift (Std.Usize.wrapping_add 20#usize 3#usize)
  let range24 ← Array.update range23 i18 q79
  let q80 ← reference_terminal.read227 openings.xor12_z 4#usize
  let q81 ← aspis_core.field.QM31.square q80
  let q82 ← aspis_core.field.QM31.sub q81 q80
  let i19 ← lift (Std.Usize.wrapping_add 20#usize 4#usize)
  let range25 ← Array.update range24 i19 q82
  f range25) = (value_owned_stage9_05 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_05 value_read_context9_05
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_05
end PV_B3P_Binding10227
