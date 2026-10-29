import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_02 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q23 ← source_read openings.z 5#usize
  let q24 ← aspis_core.field.QM31.square q23
  let q25 ← aspis_core.field.QM31.sub q24 q23
  let range6 ← Array.update state.2 5#usize q25
  let q26 ← source_read openings.z 6#usize
  let q27 ← aspis_core.field.QM31.square q26
  let q28 ← aspis_core.field.QM31.sub q27 q26
  let range7 ← Array.update range6 6#usize q28
  let q29 ← source_read openings.z 7#usize
  let q30 ← aspis_core.field.QM31.square q29
  let q31 ← aspis_core.field.QM31.sub q30 q29
  let range8 ← Array.update range7 7#usize q31
  let q32 ← source_read openings.z 8#usize
  let q33 ← aspis_core.field.QM31.square q32
  let q34 ← aspis_core.field.QM31.sub q33 q32
  let range9 ← Array.update range8 8#usize q34
  let q35 ← source_read openings.z 9#usize
  let q36 ← aspis_core.field.QM31.square q35
  let q37 ← aspis_core.field.QM31.sub q36 q35
  let range10 ← Array.update range9 9#usize q37
  Result.ok (state.1,range10)

def value_owned_stage9_02 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_02 @reference_terminal.read227 packed openings selectors state

def value_direct_stage9_02 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_02 (fun values i => Array.index_usize values i) packed openings selectors state

theorem value_stage_read_binding9_02 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_stage9_02 packed openings selectors state = value_direct_stage9_02 packed openings selectors state :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_02 @source_read packed openings selectors state) read_function_binding
#print axioms value_stage_read_binding9_02
end PV_B3P_Binding9227
