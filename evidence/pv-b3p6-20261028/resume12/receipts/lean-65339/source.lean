import PV_B3P_ValueRead907227
import PV_B3P_ReconstructBinding9227
namespace PV_B3P_Binding12227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 Result
set_option autoImplicit false
def value_context12_07 (operation : Array aspis_core.field.QM31 16#usize → Result aspis_core.field.QM31) (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q98 ← operation openings.z
  let q99 ← operation openings.succ_z
  let i25 ← lift (Std.U32.wrapping_shl 1#u32 10#u32)
  let q100 ← aspis_core.field.QM31.mul_m31 q99 i25
  let q101 ← aspis_core.field.QM31.add q98 q100
  let q102 ← operation openings.xor12_z
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
def value_stage12_07 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_context12_07 (source_reconstruct) (fun values i => Array.index_usize values i) packed openings selectors state
theorem value_stage_binding12_07 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_direct_stage9_07 packed openings selectors state = value_stage12_07 packed openings selectors state :=
  congrArg (fun (operation : Array aspis_core.field.QM31 16#usize → Result aspis_core.field.QM31) => value_context12_07 @operation
    (fun values i => Array.index_usize values i) packed openings selectors state) (funext fun view => (reconstruct_body_binding view).symm)
#print axioms value_stage_binding12_07
end PV_B3P_Binding12227
