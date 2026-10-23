import S2H_ReferencePorts
import S2D_ErrorPrefixes
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisS2OwnedStage1
namespace AspisR1.S2H
open S2E S2E_Reference.S2E_Reference

/-- Rejection retains the decoder's returned state; no statement is dropped
when no Box was returned. Native decoder error mapping/effects remain G's port. -/
theorem decode_rejected {C S : Type} (ops : S2E_Reference.Ops) (children : Children C S)
    (state after : S) (sdk : SDK) (publicInput data : Slice U8) (error : PE)
    (rejected : children.decode state publicInput = ok (.Err error,after)) :
    decoded_continuation ops children state sdk publicInput data = ok (.Err error,after,sdk) := by
  simp (config := {zeta:=true,zetaDelta:=true}) only [decoded_continuation,rejected,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from] <;> rfl

/-- Validator mapping is InvalidAccountData on the same statement and state. -/
theorem validation_rejected {C S : Type} (ops : S2E_Reference.Ops) (children : Children C S)
    (state after : S) (sdk : SDK) (statement : Statement) (publicInput data : Slice U8) (error : PE)
    (rejected : children.validate state statement = ok (.Err error,after)) :
    statement_continuation ops children state sdk statement publicInput data =
      ok (.Err solana_program_error.ProgramError.InvalidAccountData,after,sdk) := by
  simp (config := {zeta:=true,zetaDelta:=true}) only [statement_continuation,rejected,bind_tc_ok,
    S2E_Reference.core.result.Result.map_err,
    statement_continuation.closure.Insts.CoreOpsFunctionFnOnceTupleProgramErrorProgramError,
    statement_continuation.closure.Insts.CoreOpsFunctionFnOnceTupleProgramErrorProgramError.call_once,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from] <;> rfl

/-- The first child's actual rejected prefix is retained even on Allocation.
No returned checkpoint or copy/drop-checkpoint suffix is manufactured. -/
theorem first_rejected {C S : Type} (children : Children C S)
    (state after : S) (sdk : SDK) (statement : Statement)
    (publicInput proof selected : Slice U8) (split cpSlot : Usize) (error : PE)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=688#usize,«end»:=58295#usize} = ok selected)
    (rejected : children.first state statement publicInput selected split = ok (.Err error,after)) :
    first_and_copy children state sdk statement publicInput proof split cpSlot =
      ok (.Err error,after,sdk) := by
  simp (config := {zeta:=true,zetaDelta:=true}) only [first_and_copy,range,rejected,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from] <;> rfl

/-- A size mismatch follows the successful child's history and really drops
its returned checkpoint before the caller's remaining guard/statement cleanup. -/
theorem checkpoint_size_rejected {C S : Type} (children : Children C S)
    (state after : S) (sdk : SDK) (slot : Usize) (cell : OwnedDataCell)
    (checkpoint : alloc.vec.Vec U8)
    (read : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice OwnedDataCell)
      sdk.data_cells slot = ok cell)
    (mismatch : alloc.vec.Vec.len checkpoint ≠ alloc.vec.Vec.len cell.bytes)
    (dropped : children.drop_checkpoint state checkpoint = ok after) :
    after_first children state sdk slot checkpoint =
      ok (.Err solana_program_error.ProgramError.InvalidAccountData,after,sdk) := by
  have different := bne_iff_ne.mpr mismatch
  simp only [after_first,read,different,if_true,bind_tc_ok]
  dsimp only
  rw [dropped]
  rfl

/-- Stage2 has already cleared return data before rejected ASQ8 validation;
its returned state is kept and no validated statement Drop is invented. -/
theorem asq8_rejected {C S : Type} (ops : S2E_Reference.Ops) (children : Children C S)
    (o : Original S) (cleared after : S) (error : PE)
    (header : stage2Header ops o.sdk o.data = ok true)
    (clear : children.clear_return_data o.state = ok cleared)
    (rejected : children.validate_asq8 cleared o.program o.sdk o.data = ok (.Err error,after)) :
    stage2 ops children o.state o.sdk o.program o.data = ok (.Err error,after,o.sdk) := by
  rw [← stage2_evaluator_port]
  simp only [evalStage2,header,bind_tc_ok,↓reduceIte,clear,rejected,onReply] <;> rfl

/-- Rejected histories include duplicate queries, mapper effects and cleanup.
No acceptance filter or rollback of the oracle history occurs in this algebra. -/
theorem rejected_query_history {Native Input State Event Error A Query : Type}
    {E : Native} {original : Input} (select : Event → Option Query)
    (state : State) (history : List Event) (error : Error)
    (mapper : State → Error → State × List Event × Error)
    (cleanup : State → State × List Event) :
    S2D.queries select (S2D.finish
      (S2D.mapError (⟨state,history,.rejected error⟩ : S2D.Cut E original State Event Error A) mapper)
      cleanup) = history.filterMap select ++ (mapper state error).2.1.filterMap select ++
        (cleanup (mapper state error).1).2.filterMap select := by
  simp only [S2D.mapError,S2D.finish,S2D.queries,List.filterMap_append,List.append_assoc]

#print axioms decode_rejected
#print axioms validation_rejected
#print axioms first_rejected
#print axioms checkpoint_size_rejected
#print axioms asq8_rejected
#print axioms rejected_query_history
end AspisR1.S2H
