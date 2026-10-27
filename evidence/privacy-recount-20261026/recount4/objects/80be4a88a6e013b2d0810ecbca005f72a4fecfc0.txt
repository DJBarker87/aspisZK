import R1Z.PV_Ext_DiagnosticOp224Types
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_Ext_DiagnosticOp224
class ExternalFuns where
  op0 {T : Type} {E : Type} {F : Type} {O : Type} (opsfunctionFnOnceOTupleEFInst :
    core.ops.function.FnOnce O E F) :
    (core.result.Result T E) → O → Result (core.result.Result T F)
  op1 :
    (Slice aspis_statement.logup.CopyLogUpRow) → aspis_core.field.QM31 →
      Result (core.result.Result (alloc.vec.Vec aspis_core.field.QM31)
      aspis_statement.logup.LogUpError)
  op2 :
    aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestTraceV1 → Std.U64
      → aspis_core.field.QM31 → Result (core.result.Result (alloc.vec.Vec
      aspis_statement.logup.CopyLogUpRow)
      aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1)
abbrev core.result.Result.map_err [ext : ExternalFuns] := @ExternalFuns.op0 ext
abbrev aspis_statement.logup.build_copy_logup_helper [ext : ExternalFuns] := @ExternalFuns.op1 ext
abbrev aspis_statement.pool_v1.pair_forest_trace.pool_v1_pair_forest_copy_rows_v1 [ext : ExternalFuns] := @ExternalFuns.op2 ext
end PV_Ext_DiagnosticOp224
