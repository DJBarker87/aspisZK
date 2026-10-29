import PV_B3P_ValueRead906227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_06 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q83 ← reference_terminal.read227 openings.xor12_z 5#usize
  let q84 ← aspis_core.field.QM31.square q83
  let q85 ← aspis_core.field.QM31.sub q84 q83
  let i20 ← lift (Std.Usize.wrapping_add 20#usize 5#usize)
  let range26 ← Array.update range_input i20 q85
  let q86 ← reference_terminal.read227 openings.xor12_z 6#usize
  let q87 ← aspis_core.field.QM31.square q86
  let q88 ← aspis_core.field.QM31.sub q87 q86
  let i21 ← lift (Std.Usize.wrapping_add 20#usize 6#usize)
  let range27 ← Array.update range26 i21 q88
  let q89 ← reference_terminal.read227 openings.xor12_z 7#usize
  let q90 ← aspis_core.field.QM31.square q89
  let q91 ← aspis_core.field.QM31.sub q90 q89
  let i22 ← lift (Std.Usize.wrapping_add 20#usize 7#usize)
  let range28 ← Array.update range27 i22 q91
  let q92 ← reference_terminal.read227 openings.xor12_z 8#usize
  let q93 ← aspis_core.field.QM31.square q92
  let q94 ← aspis_core.field.QM31.sub q93 q92
  let i23 ← lift (Std.Usize.wrapping_add 20#usize 8#usize)
  let range29 ← Array.update range28 i23 q94
  let q95 ← reference_terminal.read227 openings.xor12_z 9#usize
  let q96 ← aspis_core.field.QM31.square q95
  let q97 ← aspis_core.field.QM31.sub q96 q95
  let i24 ← lift (Std.Usize.wrapping_add 20#usize 9#usize)
  let range30 ← Array.update range29 i24 q97
  f range30) = (value_owned_stage9_06 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_06 value_read_context9_06
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_06
end PV_B3P_Binding10227
