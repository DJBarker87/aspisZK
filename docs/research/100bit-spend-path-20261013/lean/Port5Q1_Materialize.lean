import Port4C_FlushState
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q1_Materialize
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev Model := OraclePortCheckpointStateC3.Prepared OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E

theorem exact (old : S8OwnedP6Finish.Weights) (a : verifier.Accumulator)
    (b : verifier.BatchedWeights) (sum : S7Kani3CallerTrace.Sum)
    (model : Model) (n : Nat)
    (before : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (size : a.weights.val.length=64)
    (trace : S7Kani3CallerTrace.PushTrace old (Port3_RowsInstall.toBW b) sum)
    (progress : S7JoinRowsTrace.Progress n 0 (Port3_RowsInstall.toBW b))
    (state : Port4C_QueryState.state a sum=OraclePortCheckpointStateC3.advance model n before)
    (flushed : Slice aspis_core.field.QM31)
    (run : Port3_FlushInstall.flush b a.weights.deref=ok flushed) :
    CheckpointBytes5Output.accumulator {a with weights:=⟨flushed.val,flushed.property⟩}=
      OraclePortCheckpointStateC3.advance model n before ∧ flushed.val.length=64 := by
  have exact := Port4C_FlushState.exact_state old a b sum flushed size progress.2.1 trace run
  have fields := Port4C_FlushField.accepted old b sum a.weights.deref flushed size progress.2.1 trace run
  exact ⟨exact.trans state,fields.1⟩

#print axioms exact
end AspisR1.Port5Q1_Materialize
end
