import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_00 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result ValueState9 := do
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
  let range := Array.repeat 33#usize aspis_core.field.QM31.ZERO
  Result.ok (range_selector,range)

def value_owned_stage9_00 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result ValueState9 :=
  value_read_context9_00 @reference_terminal.read227 packed openings selectors

def value_direct_stage9_00 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) : Result ValueState9 :=
  value_read_context9_00 (fun values i => Array.index_usize values i) packed openings selectors

theorem value_stage_read_binding9_00 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) :
    value_owned_stage9_00 packed openings selectors = value_direct_stage9_00 packed openings selectors :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_00 @source_read packed openings selectors) read_function_binding
#print axioms value_stage_read_binding9_00
end PV_B3P_Binding9227
