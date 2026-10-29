import PV_B3P_ValueRead900227
import PV_B3P_Ordered227
import PV_B3P_DigestCpsEq9227
namespace PV_B3P_Binding10227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false

def value_selector10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result aspis_core.field.QM31 := do
  let i ←
    lift (Std.Usize.wrapping_mul 16#usize
      reference_terminal.VALUE_AUXILIARY_BLOCK)
  let q ← reference_copy_terminal.Selectors.row selectors i
  let i1 ←
    lift (Std.Usize.wrapping_mul 16#usize
      reference_terminal.VALUE_AUXILIARY_BLOCK)
  let i2 ← lift (Std.Usize.wrapping_add i1 2#usize)
  let q1 ← reference_copy_terminal.Selectors.row selectors i2
  let i3 ←
    lift (Std.Usize.wrapping_mul 16#usize
      reference_terminal.VALUE_AUXILIARY_BLOCK)
  let i4 ← lift (Std.Usize.wrapping_add i3 4#usize)
  let q2 ← reference_copy_terminal.Selectors.row selectors i4
  let q3 ← Array.index_usize (Array.make 3#usize [ q, q1, q2 ] (by simp only [List.length_cons,List.length_nil]; rfl)) 0#usize
  let q4 ← aspis_core.field.QM31.add aspis_core.field.QM31.ZERO q3
  let q5 ← Array.index_usize (Array.make 3#usize [ q, q1, q2 ] (by simp only [List.length_cons,List.length_nil]; rfl)) 1#usize
  let q6 ← aspis_core.field.QM31.add q4 q5
  let q7 ← Array.index_usize (Array.make 3#usize [ q, q1, q2 ] (by simp only [List.length_cons,List.length_nil]; rfl)) 2#usize
  let range_selector ← aspis_core.field.QM31.add q6 q7

  .ok range_selector

attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.sub aspis_core.field.QM31.square aspis_core.field.QM31.mul aspis_core.field.QM31.mul_m31 Array.index_usize Array.update reference_terminal.read227 reference_terminal.reconstruct_10 reference_terminal.add_preweighted reference_copy_terminal.Selectors.row

theorem value_head_cps10_00 {β : Type} (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (f : aspis_core.field.QM31 → Result β) :
    (do
  let i ←
    lift (Std.Usize.wrapping_mul 16#usize
      reference_terminal.VALUE_AUXILIARY_BLOCK)
  let q ← reference_copy_terminal.Selectors.row selectors i
  let i1 ←
    lift (Std.Usize.wrapping_mul 16#usize
      reference_terminal.VALUE_AUXILIARY_BLOCK)
  let i2 ← lift (Std.Usize.wrapping_add i1 2#usize)
  let q1 ← reference_copy_terminal.Selectors.row selectors i2
  let i3 ←
    lift (Std.Usize.wrapping_mul 16#usize
      reference_terminal.VALUE_AUXILIARY_BLOCK)
  let i4 ← lift (Std.Usize.wrapping_add i3 4#usize)
  let q2 ← reference_copy_terminal.Selectors.row selectors i4
  let q3 ← Array.index_usize (Array.make 3#usize [ q, q1, q2 ] (by simp only [List.length_cons,List.length_nil]; rfl)) 0#usize
  let q4 ← aspis_core.field.QM31.add aspis_core.field.QM31.ZERO q3
  let q5 ← Array.index_usize (Array.make 3#usize [ q, q1, q2 ] (by simp only [List.length_cons,List.length_nil]; rfl)) 1#usize
  let q6 ← aspis_core.field.QM31.add q4 q5
  let q7 ← Array.index_usize (Array.make 3#usize [ q, q1, q2 ] (by simp only [List.length_cons,List.length_nil]; rfl)) 2#usize
  let range_selector ← aspis_core.field.QM31.add q6 q7

  f range_selector) = (value_selector10 packed openings selectors >>= f) := by
  unfold value_selector10
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  rfl

theorem value_selector_pair10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    value_owned_stage9_00 packed openings selectors = (do
      let selector ← value_selector10 packed openings selectors
      .ok (selector,Array.repeat 33#usize aspis_core.field.QM31.ZERO)) := by
  unfold value_owned_stage9_00 value_read_context9_00 value_selector10
  conv_rhs => simp only [PV_B3P_Ordered227.bind_assoc,bind_tc_ok]
  rfl
#print axioms value_selector_pair10

#print axioms value_head_cps10_00
end PV_B3P_Binding10227
