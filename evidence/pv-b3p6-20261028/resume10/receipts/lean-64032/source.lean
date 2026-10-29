import PV_B3P_ValueRead904227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_04 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q53 ← reference_terminal.read227 openings.succ_z 5#usize
  let q54 ← aspis_core.field.QM31.square q53
  let q55 ← aspis_core.field.QM31.sub q54 q53
  let i10 ← lift (Std.Usize.wrapping_add 10#usize 5#usize)
  let range16 ← Array.update range_input i10 q55
  let q56 ← reference_terminal.read227 openings.succ_z 6#usize
  let q57 ← aspis_core.field.QM31.square q56
  let q58 ← aspis_core.field.QM31.sub q57 q56
  let i11 ← lift (Std.Usize.wrapping_add 10#usize 6#usize)
  let range17 ← Array.update range16 i11 q58
  let q59 ← reference_terminal.read227 openings.succ_z 7#usize
  let q60 ← aspis_core.field.QM31.square q59
  let q61 ← aspis_core.field.QM31.sub q60 q59
  let i12 ← lift (Std.Usize.wrapping_add 10#usize 7#usize)
  let range18 ← Array.update range17 i12 q61
  let q62 ← reference_terminal.read227 openings.succ_z 8#usize
  let q63 ← aspis_core.field.QM31.square q62
  let q64 ← aspis_core.field.QM31.sub q63 q62
  let i13 ← lift (Std.Usize.wrapping_add 10#usize 8#usize)
  let range19 ← Array.update range18 i13 q64
  let q65 ← reference_terminal.read227 openings.succ_z 9#usize
  let q66 ← aspis_core.field.QM31.square q65
  let q67 ← aspis_core.field.QM31.sub q66 q65
  let i14 ← lift (Std.Usize.wrapping_add 10#usize 9#usize)
  let range20 ← Array.update range19 i14 q67
  f range20) = (value_owned_stage9_04 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_04 value_read_context9_04
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_04
end PV_B3P_Binding10227
