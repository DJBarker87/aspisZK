import PV_B3P_P227_08
import PV_B3P_ReadFunctions9227
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227 Result ControlFlow Error
set_option autoImplicit false

/-- Exact emitted body context; only the immutable-read callee is abstracted. -/
def reference_terminal_validate_transition_loop_body_read_context9 (source_read : (Array (Array U32 8#usize) 20#usize → Usize → Result (Array U32 8#usize))) (index : Std.U64) (a : Array (Array aspis_core.field.M31 8#usize) 20#usize)
  (a1 : Array (Array aspis_core.field.M31 8#usize) 20#usize)
  (carry : Std.Usize) (level_index : Std.Usize)  :
  Result (ControlFlow Std.Usize (Option (core.result.Result Unit
    reference_terminal.PoolV1PairForestSemanticTerminalErrorV1))) :=  do
  if level_index < 20#usize
  then
    let level_index1 ← lift (Std.Usize.wrapping_add level_index 1#usize)
    if level_index = carry
    then
      if carry < 20#usize
      then ok (cont level_index1)
      else
        let expected ←
          if level_index < carry
          then reference_terminal.empty_root level_index
          else
            do
            let i ← lift (Std.U64.wrapping_shr index (UScalar.cast .U32 level_index))
            let i1 ← lift (i &&& 1#u64)
            if i1 = 0#u64
            then reference_terminal.empty_root level_index
            else source_read a level_index
        let a2 ← source_read a1 level_index
        let b ←
          core.array.equality.PartialEqArray.ne
            aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a2 expected
        if b
        then
          ok (done (some (core.result.Result.Err
            reference_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)))
        else ok (cont level_index1)
    else
      let expected ←
        if level_index < carry
        then reference_terminal.empty_root level_index
        else
          do
          let i ← lift (Std.U64.wrapping_shr index (UScalar.cast .U32 level_index))
          let i1 ← lift (i &&& 1#u64)
          if i1 = 0#u64
          then reference_terminal.empty_root level_index
          else source_read a level_index
      let a2 ← source_read a1 level_index
      let b ←
        core.array.equality.PartialEqArray.ne
          aspis_core.field.M31.Insts.CoreCmpPartialEqM31 a2 expected
      if b
      then
        ok (done (some (core.result.Result.Err
          reference_terminal.PoolV1PairForestSemanticTerminalErrorV1.InvalidAppendTransition)))
      else ok (cont level_index1)
  else ok (done none)

def reference_terminal_validate_transition_loop_body_direct_read9 (index : Std.U64) (a : Array (Array aspis_core.field.M31 8#usize) 20#usize)
  (a1 : Array (Array aspis_core.field.M31 8#usize) 20#usize)
  (carry : Std.Usize) (level_index : Std.Usize)  :
  Result (ControlFlow Std.Usize (Option (core.result.Result Unit
    reference_terminal.PoolV1PairForestSemanticTerminalErrorV1))) :=
  reference_terminal_validate_transition_loop_body_read_context9 (fun values i => Array.index_usize values i) index a a1 carry level_index

theorem reference_terminal_validate_transition_loop_body_read_binding9 (index : Std.U64) (a : Array (Array aspis_core.field.M31 8#usize) 20#usize)
  (a1 : Array (Array aspis_core.field.M31 8#usize) 20#usize)
  (carry : Std.Usize) (level_index : Std.Usize)  :
    reference_terminal.validate_transition_loop.body index a a1 carry level_index = reference_terminal_validate_transition_loop_body_direct_read9 index a a1 carry level_index :=
  congrArg (fun source_read => reference_terminal_validate_transition_loop_body_read_context9 source_read index a a1 carry level_index) digest_function_binding

#print axioms reference_terminal_validate_transition_loop_body_read_binding9
end PV_B3P_Binding9227
