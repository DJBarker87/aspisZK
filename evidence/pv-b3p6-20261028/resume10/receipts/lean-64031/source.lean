import PV_B3P_ValueRead903227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_03 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (range_selector : aspis_core.field.QM31) (range_input : Array aspis_core.field.QM31 33#usize) (f : Array aspis_core.field.QM31 33#usize → Result β) :
    (do
  let q38 ← reference_terminal.read227 openings.succ_z 0#usize
  let q39 ← aspis_core.field.QM31.square q38
  let q40 ← aspis_core.field.QM31.sub q39 q38
  let i5 ← lift (Std.Usize.wrapping_add 10#usize 0#usize)
  let range11 ← Array.update range_input i5 q40
  let q41 ← reference_terminal.read227 openings.succ_z 1#usize
  let q42 ← aspis_core.field.QM31.square q41
  let q43 ← aspis_core.field.QM31.sub q42 q41
  let i6 ← lift (Std.Usize.wrapping_add 10#usize 1#usize)
  let range12 ← Array.update range11 i6 q43
  let q44 ← reference_terminal.read227 openings.succ_z 2#usize
  let q45 ← aspis_core.field.QM31.square q44
  let q46 ← aspis_core.field.QM31.sub q45 q44
  let i7 ← lift (Std.Usize.wrapping_add 10#usize 2#usize)
  let range13 ← Array.update range12 i7 q46
  let q47 ← reference_terminal.read227 openings.succ_z 3#usize
  let q48 ← aspis_core.field.QM31.square q47
  let q49 ← aspis_core.field.QM31.sub q48 q47
  let i8 ← lift (Std.Usize.wrapping_add 10#usize 3#usize)
  let range14 ← Array.update range13 i8 q49
  let q50 ← reference_terminal.read227 openings.succ_z 4#usize
  let q51 ← aspis_core.field.QM31.square q50
  let q52 ← aspis_core.field.QM31.sub q51 q50
  let i9 ← lift (Std.Usize.wrapping_add 10#usize 4#usize)
  let range15 ← Array.update range14 i9 q52
  f range15) = (value_owned_stage9_03 packed openings selectors (range_selector,range_input) >>= (fun next => f next.2)) := by
  unfold value_owned_stage9_03 value_read_context9_03
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]

#print axioms value_head_cps10_03
end PV_B3P_Binding10227
