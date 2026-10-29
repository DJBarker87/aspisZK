import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_10 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q132 ← source_read state.2 12#usize
  let q133 ← aspis_core.field.QM31.mul state.1 q132
  let range46 ← Array.update state.2 12#usize q133
  let q134 ← source_read range46 13#usize
  let q135 ← aspis_core.field.QM31.mul state.1 q134
  let range47 ← Array.update range46 13#usize q135
  let q136 ← source_read range47 14#usize
  let q137 ← aspis_core.field.QM31.mul state.1 q136
  let range48 ← Array.update range47 14#usize q137
  let q138 ← source_read range48 15#usize
  let q139 ← aspis_core.field.QM31.mul state.1 q138
  let range49 ← Array.update range48 15#usize q139
  let q140 ← source_read range49 16#usize
  let q141 ← aspis_core.field.QM31.mul state.1 q140
  let range50 ← Array.update range49 16#usize q141
  let q142 ← source_read range50 17#usize
  let q143 ← aspis_core.field.QM31.mul state.1 q142
  let range51 ← Array.update range50 17#usize q143
  Result.ok (state.1,range51)

def value_owned_stage9_10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_10 @reference_terminal.read227 packed openings selectors state

def value_direct_stage9_10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_10 (fun values i => Array.index_usize values i) packed openings selectors state

theorem value_stage_read_binding9_10 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_stage9_10 packed openings selectors state = value_direct_stage9_10 packed openings selectors state :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_10 @source_read packed openings selectors state) read_function_binding
#print axioms value_stage_read_binding9_10
end PV_B3P_Binding9227
