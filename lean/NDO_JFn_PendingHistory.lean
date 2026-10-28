import NDO_JFo_Pending
import Port4C_RowMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFn_PendingHistory
open Aeneas Aeneas.Std Result AspisR1Stage2

def old := Port3_PendingInstall.owned JFo_Prepared.accumulator.weights.deref
def sum := S7Kani3CallerTrace.initialSum old

theorem reference : Port3_PendingInstall.pending true JFo_Prepared.accumulator.weights.deref=ok (.Ok JFo_Pending.value) := by
  rw [←Port3_NativePendingInstall.reference_eq true (JFo_Prepared.accumulator.weights.deref) JFo_Prepared.weights_length]
  exact JFo_Pending.source

theorem trace : S7Kani3CallerTrace.PushTrace old
    (Port3_RowsInstall.toBW JFo_Pending.value) sum :=
  Port3_PendingInstall.accepted_trace true _ _ reference

theorem progress : S7JoinRowsTrace.Progress 0 0 (Port3_RowsInstall.toBW JFo_Pending.value) :=
  Port3_PendingInstall.accepted_progress true _ _ JFo_Prepared.weights_length reference

#print axioms reference
#print axioms trace
#print axioms progress
end AspisR1.JFn_PendingHistory
end
