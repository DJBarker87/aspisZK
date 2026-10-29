import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_13 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q168 ← source_read state.2 30#usize
  let q169 ← aspis_core.field.QM31.mul state.1 q168
  let range64 ← Array.update state.2 30#usize q169
  let q170 ← source_read range64 31#usize
  let q171 ← aspis_core.field.QM31.mul state.1 q170
  let range65 ← Array.update range64 31#usize q171
  let q172 ← source_read range65 32#usize
  let q173 ← aspis_core.field.QM31.mul state.1 q172
  let range66 ← Array.update range65 32#usize q173
  Result.ok (state.1,range66)

def value_owned_stage9_13 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_13 @reference_terminal.read227 packed openings selectors state

def value_direct_stage9_13 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_13 (fun values i => Array.index_usize values i) packed openings selectors state

theorem value_stage_read_binding9_13 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_stage9_13 packed openings selectors state = value_direct_stage9_13 packed openings selectors state :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_13 @source_read packed openings selectors state) read_function_binding
#print axioms value_stage_read_binding9_13
end PV_B3P_Binding9227
