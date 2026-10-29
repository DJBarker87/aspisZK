import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_12 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q156 ← source_read state.2 24#usize
  let q157 ← aspis_core.field.QM31.mul state.1 q156
  let range58 ← Array.update state.2 24#usize q157
  let q158 ← source_read range58 25#usize
  let q159 ← aspis_core.field.QM31.mul state.1 q158
  let range59 ← Array.update range58 25#usize q159
  let q160 ← source_read range59 26#usize
  let q161 ← aspis_core.field.QM31.mul state.1 q160
  let range60 ← Array.update range59 26#usize q161
  let q162 ← source_read range60 27#usize
  let q163 ← aspis_core.field.QM31.mul state.1 q162
  let range61 ← Array.update range60 27#usize q163
  let q164 ← source_read range61 28#usize
  let q165 ← aspis_core.field.QM31.mul state.1 q164
  let range62 ← Array.update range61 28#usize q165
  let q166 ← source_read range62 29#usize
  let q167 ← aspis_core.field.QM31.mul state.1 q166
  let range63 ← Array.update range62 29#usize q167
  Result.ok (state.1,range63)

def value_owned_stage9_12 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_12 @reference_terminal.read227 packed openings selectors state

def value_direct_stage9_12 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_12 (fun values i => Array.index_usize values i) packed openings selectors state

theorem value_stage_read_binding9_12 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_stage9_12 packed openings selectors state = value_direct_stage9_12 packed openings selectors state :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_12 @source_read packed openings selectors state) read_function_binding
#print axioms value_stage_read_binding9_12
end PV_B3P_Binding9227
