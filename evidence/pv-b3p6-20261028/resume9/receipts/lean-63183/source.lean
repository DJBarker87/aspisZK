import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_07 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q98 ← reference_terminal.reconstruct_10 openings.z
  let q99 ← reference_terminal.reconstruct_10 openings.succ_z
  let i25 ← lift (Std.U32.wrapping_shl 1#u32 10#u32)
  let q100 ← aspis_core.field.QM31.mul_m31 q99 i25
  let q101 ← aspis_core.field.QM31.add q98 q100
  let q102 ← reference_terminal.reconstruct_10 openings.xor12_z
  let i26 ← lift (Std.U32.wrapping_shl 1#u32 20#u32)
  let q103 ← aspis_core.field.QM31.mul_m31 q102 i26
  let reconstructed ← aspis_core.field.QM31.add q101 q103
  let q104 ← Array.index_usize openings.z 10#usize
  let q105 ← aspis_core.field.QM31.sub q104 reconstructed
  let range31 ← Array.update state.2 30#usize q105
  let q106 ← Array.index_usize openings.succ_z 10#usize
  let range32 ← Array.update range31 31#usize q106
  let q107 ← Array.index_usize openings.xor12_z 10#usize
  let range33 ← Array.update range32 32#usize q107
  Result.ok (state.1,range33)

def value_owned_stage9_07 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_07 @reference_terminal.read227 packed openings selectors state

def value_direct_stage9_07 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_07 (fun values i => Array.index_usize values i) packed openings selectors state

theorem value_stage_read_binding9_07 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_stage9_07 packed openings selectors state = value_direct_stage9_07 packed openings selectors state :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_07 @source_read packed openings selectors state) read_function_binding
#print axioms value_stage_read_binding9_07
end PV_B3P_Binding9227
