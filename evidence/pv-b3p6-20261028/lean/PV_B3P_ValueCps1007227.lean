import PV_B3P_ValueRead907227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_07 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q98 ← reference_terminal.reconstruct_10 openings.z
  let q99 ← reference_terminal.reconstruct_10 openings.succ_z
  let i25 ← lift (Std.U32.wrapping_shl 1#u32 10#u32)
  let q100 ← aspis_core.field.QM31.mul_m31 q99 i25
  let q101 ← aspis_core.field.QM31.add q98 q100
  let q102 ← reference_terminal.reconstruct_10 openings.xor12_z
  let i26 ← lift (Std.U32.wrapping_shl 1#u32 20#u32)
  let q103 ← aspis_core.field.QM31.mul_m31 q102 i26
  let reconstructed ← aspis_core.field.QM31.add q101 q103
  let q104 ← Array.index_usize openings.z 10#usize
  let q105 ← aspis_core.field.QM31.sub q104 reconstructed
  let range31 ← Array.update range_input 30#usize q105
  let q106 ← Array.index_usize openings.succ_z 10#usize
  let range32 ← Array.update range31 31#usize q106
  let q107 ← Array.index_usize openings.xor12_z 10#usize
  let range33 ← Array.update range32 32#usize q107
  f range33) = (value_owned_stage9_07 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_07 value_read_context9_07
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_07
end PV_B3P_Binding10227
