import FJl_SourceSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_PhaseSlots
open Aeneas Aeneas.Std Result
/-- Both actual phase dictionaries retain the installed opening, dot, circle and comparison. -/
theorem value {C : Type} (err : C) (seed : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) (early : Bool) :
    let c := FIp_Install.configuration err seed r
    let ops := if early then Tx1Q_QueryBridge.leaves c.query else
      Port3_QueryStage.release (Port4C_RowStd.install (Port5Q1_QueryPorts.install c.query))
    ops.op11=Port4B_Opening.opening ∧ ops.op20=FIp_DotsAdapter.dots ∧
    ops.op17=c.query.op17 ∧ ops.widePartialEq=c.query.widePartialEq := by
  cases early <;> exact ⟨rfl,rfl,rfl,rfl⟩
#print axioms value
end AspisR1.FJo_PhaseSlots
end
