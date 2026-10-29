import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_11 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q144 ← source_read state.2 18#usize
  let q145 ← aspis_core.field.QM31.mul state.1 q144
  let range52 ← Array.update state.2 18#usize q145
  let q146 ← source_read range52 19#usize
  let q147 ← aspis_core.field.QM31.mul state.1 q146
  let range53 ← Array.update range52 19#usize q147
  let q148 ← source_read range53 20#usize
  let q149 ← aspis_core.field.QM31.mul state.1 q148
  let range54 ← Array.update range53 20#usize q149
  let q150 ← source_read range54 21#usize
  let q151 ← aspis_core.field.QM31.mul state.1 q150
  let range55 ← Array.update range54 21#usize q151
  let q152 ← source_read range55 22#usize
  let q153 ← aspis_core.field.QM31.mul state.1 q152
  let range56 ← Array.update range55 22#usize q153
  let q154 ← source_read range56 23#usize
  let q155 ← aspis_core.field.QM31.mul state.1 q154
  let range57 ← Array.update range56 23#usize q155
  Result.ok (state.1,range57)

def value_owned_stage9_11 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_11 @reference_terminal.read227 packed openings selectors state

def value_direct_stage9_11 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_11 (fun values i => Array.index_usize values i) packed openings selectors state

theorem value_stage_read_binding9_11 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_stage9_11 packed openings selectors state = value_direct_stage9_11 packed openings selectors state :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_11 @source_read packed openings selectors state) read_function_binding
#print axioms value_stage_read_binding9_11
end PV_B3P_Binding9227
