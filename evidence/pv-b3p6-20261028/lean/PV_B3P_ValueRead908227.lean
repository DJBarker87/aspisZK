import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_08 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q108 ← source_read state.2 0#usize
  let q109 ← aspis_core.field.QM31.mul state.1 q108
  let range34 ← Array.update state.2 0#usize q109
  let q110 ← source_read range34 1#usize
  let q111 ← aspis_core.field.QM31.mul state.1 q110
  let range35 ← Array.update range34 1#usize q111
  let q112 ← source_read range35 2#usize
  let q113 ← aspis_core.field.QM31.mul state.1 q112
  let range36 ← Array.update range35 2#usize q113
  let q114 ← source_read range36 3#usize
  let q115 ← aspis_core.field.QM31.mul state.1 q114
  let range37 ← Array.update range36 3#usize q115
  let q116 ← source_read range37 4#usize
  let q117 ← aspis_core.field.QM31.mul state.1 q116
  let range38 ← Array.update range37 4#usize q117
  let q118 ← source_read range38 5#usize
  let q119 ← aspis_core.field.QM31.mul state.1 q118
  let range39 ← Array.update range38 5#usize q119
  Result.ok (state.1,range39)

def value_owned_stage9_08 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_08 @reference_terminal.read227 packed openings selectors state

def value_direct_stage9_08 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_08 (fun values i => Array.index_usize values i) packed openings selectors state

theorem value_stage_read_binding9_08 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_stage9_08 packed openings selectors state = value_direct_stage9_08 packed openings selectors state :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_08 @source_read packed openings selectors state) read_function_binding
#print axioms value_stage_read_binding9_08
end PV_B3P_Binding9227
