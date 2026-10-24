import Port4C_FlushField
import Port4C_QueryState

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_FlushState
open Aeneas Aeneas.Std Result AspisR1Stage2

/-- The SAME successful retained flush materializes the virtual query state
under the checkpoint's existing total decoder. No fresh mathematical state
or successful alternative flush is selected. -/
theorem exact_state (old : S8OwnedP6Finish.Weights) (a : verifier.Accumulator)
    (b : verifier.BatchedWeights) (sum : S7Kani3CallerTrace.Sum)
    (flushed : Slice aspis_core.field.QM31)
    (size : a.weights.val.length=64) (rawSize : b.raw.val.length=64)
    (trace : S7Kani3CallerTrace.PushTrace old (Port3_RowsInstall.toBW b) sum)
    (run : Port3_FlushInstall.flush b a.weights.deref=ok flushed) :
    CheckpointBytes5Output.accumulator
      {a with weights:=⟨flushed.val,flushed.property⟩}=Port4C_QueryState.state a sum := by
  have fields := Port4C_FlushField.accepted old b sum a.weights.deref flushed size rawSize trace run
  unfold CheckpointBytes5Output.accumulator Port4C_QueryState.state
  congr 1
  funext i
  exact fields.2 i

#print axioms exact_state
end AspisR1.Port4C_FlushState
end
