import RPt_JFo_Prepared
import RPz7_Tx2N_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFo_Pending
open Aeneas Aeneas.Std Result AspisR1Stage2

def value : verifier.BatchedWeights :=
  ⟨Port3_PendingInstall.raw JFo_Prepared.accumulator.weights.deref,0#usize⟩

theorem source : Port3_NativePendingInstall.source true JFo_Prepared.accumulator.weights.deref =
    ok (.Ok value) := by
  rw [Port3_NativePendingInstall.source,
    Port3_NativePendingInstall.emitted_exact true (JFo_Prepared.accumulator.weights.deref) JFo_Prepared.weights_length]
  rfl

theorem length : value.raw.val.length=64 := by
  exact (Port3_NativePendingInstall.accepted_fields true _ value
    JFo_Prepared.weights_length source).2.2.2

theorem terms : value.terms=0#usize := rfl

#print axioms source
#print axioms length
#print axioms terms
end AspisR1.JFo_Pending
end
