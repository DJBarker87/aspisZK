import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_09 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q120 ← source_read state.2 6#usize
  let q121 ← aspis_core.field.QM31.mul state.1 q120
  let range40 ← Array.update state.2 6#usize q121
  let q122 ← source_read range40 7#usize
  let q123 ← aspis_core.field.QM31.mul state.1 q122
  let range41 ← Array.update range40 7#usize q123
  let q124 ← source_read range41 8#usize
  let q125 ← aspis_core.field.QM31.mul state.1 q124
  let range42 ← Array.update range41 8#usize q125
  let q126 ← source_read range42 9#usize
  let q127 ← aspis_core.field.QM31.mul state.1 q126
  let range43 ← Array.update range42 9#usize q127
  let q128 ← source_read range43 10#usize
  let q129 ← aspis_core.field.QM31.mul state.1 q128
  let range44 ← Array.update range43 10#usize q129
  let q130 ← source_read range44 11#usize
  let q131 ← aspis_core.field.QM31.mul state.1 q130
  let range45 ← Array.update range44 11#usize q131
  Result.ok (state.1,range45)

def value_owned_stage9_09 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_09 @reference_terminal.read227 packed openings selectors state

def value_direct_stage9_09 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_09 (fun values i => Array.index_usize values i) packed openings selectors state

theorem value_stage_read_binding9_09 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_stage9_09 packed openings selectors state = value_direct_stage9_09 packed openings selectors state :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_09 @source_read packed openings selectors state) read_function_binding
#print axioms value_stage_read_binding9_09
end PV_B3P_Binding9227
