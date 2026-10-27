import FJo_PhaseSlots
set_option autoImplicit false
namespace AspisR1.FJo_PhaseSame
/-- Phase adapters install the SAME query dictionary; only execution operands differ. -/
theorem value (ops : Port3_NativeQueryBody.Ops) :
    Tx1Q_QueryBridge.leaves ops=
      Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install ops)) := rfl
#print axioms value
end AspisR1.FJo_PhaseSame
