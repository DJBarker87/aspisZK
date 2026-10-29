import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_06 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q83 ← source_read openings.xor12_z 5#usize
  let q84 ← aspis_core.field.QM31.square q83
  let q85 ← aspis_core.field.QM31.sub q84 q83
  let i20 ← lift (Std.Usize.wrapping_add 20#usize 5#usize)
  let range26 ← Array.update state.2 i20 q85
  let q86 ← source_read openings.xor12_z 6#usize
  let q87 ← aspis_core.field.QM31.square q86
  let q88 ← aspis_core.field.QM31.sub q87 q86
  let i21 ← lift (Std.Usize.wrapping_add 20#usize 6#usize)
  let range27 ← Array.update range26 i21 q88
  let q89 ← source_read openings.xor12_z 7#usize
  let q90 ← aspis_core.field.QM31.square q89
  let q91 ← aspis_core.field.QM31.sub q90 q89
  let i22 ← lift (Std.Usize.wrapping_add 20#usize 7#usize)
  let range28 ← Array.update range27 i22 q91
  let q92 ← source_read openings.xor12_z 8#usize
  let q93 ← aspis_core.field.QM31.square q92
  let q94 ← aspis_core.field.QM31.sub q93 q92
  let i23 ← lift (Std.Usize.wrapping_add 20#usize 8#usize)
  let range29 ← Array.update range28 i23 q94
  let q95 ← source_read openings.xor12_z 9#usize
  let q96 ← aspis_core.field.QM31.square q95
  let q97 ← aspis_core.field.QM31.sub q96 q95
  let i24 ← lift (Std.Usize.wrapping_add 20#usize 9#usize)
  let range30 ← Array.update range29 i24 q97
  Result.ok (state.1,range30)

def value_owned_stage9_06 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_06 @reference_terminal.read227 packed openings selectors state

def value_direct_stage9_06 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_06 (fun values i => Array.index_usize values i) packed openings selectors state

theorem value_stage_read_binding9_06 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_stage9_06 packed openings selectors state = value_direct_stage9_06 packed openings selectors state :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_06 @source_read packed openings selectors state) read_function_binding
#print axioms value_stage_read_binding9_06
end PV_B3P_Binding9227
