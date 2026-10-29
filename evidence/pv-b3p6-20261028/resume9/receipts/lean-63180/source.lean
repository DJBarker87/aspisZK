import PV_B3P_ValueReadTypes9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

def value_read_context9_04 (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 := do
  let q53 ← source_read openings.succ_z 5#usize
  let q54 ← aspis_core.field.QM31.square q53
  let q55 ← aspis_core.field.QM31.sub q54 q53
  let i10 ← lift (Std.Usize.wrapping_add 10#usize 5#usize)
  let range16 ← Array.update state.2 i10 q55
  let q56 ← source_read openings.succ_z 6#usize
  let q57 ← aspis_core.field.QM31.square q56
  let q58 ← aspis_core.field.QM31.sub q57 q56
  let i11 ← lift (Std.Usize.wrapping_add 10#usize 6#usize)
  let range17 ← Array.update range16 i11 q58
  let q59 ← source_read openings.succ_z 7#usize
  let q60 ← aspis_core.field.QM31.square q59
  let q61 ← aspis_core.field.QM31.sub q60 q59
  let i12 ← lift (Std.Usize.wrapping_add 10#usize 7#usize)
  let range18 ← Array.update range17 i12 q61
  let q62 ← source_read openings.succ_z 8#usize
  let q63 ← aspis_core.field.QM31.square q62
  let q64 ← aspis_core.field.QM31.sub q63 q62
  let i13 ← lift (Std.Usize.wrapping_add 10#usize 8#usize)
  let range19 ← Array.update range18 i13 q64
  let q65 ← source_read openings.succ_z 9#usize
  let q66 ← aspis_core.field.QM31.square q65
  let q67 ← aspis_core.field.QM31.sub q66 q65
  let i14 ← lift (Std.Usize.wrapping_add 10#usize 9#usize)
  let range20 ← Array.update range19 i14 q67
  Result.ok (state.1,range20)

def value_owned_stage9_04 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_04 @reference_terminal.read227 packed openings selectors state

def value_direct_stage9_04 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) : Result ValueState9 :=
  value_read_context9_04 (fun values i => Array.index_usize values i) packed openings selectors state

theorem value_stage_read_binding9_04 (packed : Array aspis_core.field.QM31 24#usize)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors) (state : ValueState9) :
    value_owned_stage9_04 packed openings selectors state = value_direct_stage9_04 packed openings selectors state :=
  congrArg (fun (source_read : ({N : Usize} → Array aspis_core.field.QM31 N → Usize → Result aspis_core.field.QM31)) => value_read_context9_04 @source_read packed openings selectors state) read_function_binding
#print axioms value_stage_read_binding9_04
end PV_B3P_Binding9227
