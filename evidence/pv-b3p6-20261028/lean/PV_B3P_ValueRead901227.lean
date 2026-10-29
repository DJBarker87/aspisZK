import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_01 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q8 ← source_read openings.z 0#usize
  let q9 ← aspis_core.field.QM31.square q8
  let q10 ← aspis_core.field.QM31.sub q9 q8
  let range1 ← Array.update state.2 0#usize q10
  let q11 ← source_read openings.z 1#usize
  let q12 ← aspis_core.field.QM31.square q11
  let q13 ← aspis_core.field.QM31.sub q12 q11
  let range2 ← Array.update range1 1#usize q13
  let q14 ← source_read openings.z 2#usize
  let q15 ← aspis_core.field.QM31.square q14
  let q16 ← aspis_core.field.QM31.sub q15 q14
  let range3 ← Array.update range2 2#usize q16
  let q17 ← source_read openings.z 3#usize
  let q18 ← aspis_core.field.QM31.square q17
  let q19 ← aspis_core.field.QM31.sub q18 q17
  let range4 ← Array.update range3 3#usize q19
  let q20 ← source_read openings.z 4#usize
  let q21 ← aspis_core.field.QM31.square q20
  let q22 ← aspis_core.field.QM31.sub q21 q20
  let range5 ← Array.update range4 4#usize q22
  Result.ok (state.1,range5)

def value_owned_stage9_01 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_01 @reference_terminal.read227 packed openings selectors state

def value_direct_stage9_01 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_01 (fun values i => Array.index_usize values i) packed openings selectors state

theorem value_stage_read_binding9_01 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_stage9_01 packed openings selectors state = value_direct_stage9_01 packed openings selectors state :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_01 @source_read packed openings selectors state) read_function_binding
#print axioms value_stage_read_binding9_01
end PV_B3P_Binding9227
