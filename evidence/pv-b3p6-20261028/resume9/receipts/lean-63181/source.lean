import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_05 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q68 ← source_read openings.xor12_z 0#usize
  let q69 ← aspis_core.field.QM31.square q68
  let q70 ← aspis_core.field.QM31.sub q69 q68
  let i15 ← lift (Std.Usize.wrapping_add 20#usize 0#usize)
  let range21 ← Array.update state.2 i15 q70
  let q71 ← source_read openings.xor12_z 1#usize
  let q72 ← aspis_core.field.QM31.square q71
  let q73 ← aspis_core.field.QM31.sub q72 q71
  let i16 ← lift (Std.Usize.wrapping_add 20#usize 1#usize)
  let range22 ← Array.update range21 i16 q73
  let q74 ← source_read openings.xor12_z 2#usize
  let q75 ← aspis_core.field.QM31.square q74
  let q76 ← aspis_core.field.QM31.sub q75 q74
  let i17 ← lift (Std.Usize.wrapping_add 20#usize 2#usize)
  let range23 ← Array.update range22 i17 q76
  let q77 ← source_read openings.xor12_z 3#usize
  let q78 ← aspis_core.field.QM31.square q77
  let q79 ← aspis_core.field.QM31.sub q78 q77
  let i18 ← lift (Std.Usize.wrapping_add 20#usize 3#usize)
  let range24 ← Array.update range23 i18 q79
  let q80 ← source_read openings.xor12_z 4#usize
  let q81 ← aspis_core.field.QM31.square q80
  let q82 ← aspis_core.field.QM31.sub q81 q80
  let i19 ← lift (Std.Usize.wrapping_add 20#usize 4#usize)
  let range25 ← Array.update range24 i19 q82
  Result.ok (state.1,range25)

def value_owned_stage9_05 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_05 @reference_terminal.read227 packed openings selectors state

def value_direct_stage9_05 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_05 (fun values i => Array.index_usize values i) packed openings selectors state

theorem value_stage_read_binding9_05 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_stage9_05 packed openings selectors state = value_direct_stage9_05 packed openings selectors state :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_05 @source_read packed openings selectors state) read_function_binding
#print axioms value_stage_read_binding9_05
end PV_B3P_Binding9227
