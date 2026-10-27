import FJl_PairExtraction
import FIp_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_SourceSlots
open Aeneas Aeneas.Std Result
/-- The phase-specific installed dictionaries preserve the SAME backend and
opening reads. No replacement call semantics are assumed. -/
theorem installed {C : Type} (err : C) (c : DrvC_Installation.Configuration FIo_Install.W C)
    (r : NP6_StdModel.Reservation) :
    (Tx1Q_QueryBridge.leaves (FIp_Install.configuration err c r).query).op20=FIp_DotsAdapter.dots ∧
    (Port3_QueryStage.release (Port4C_RowStd.install
      (Port5Q1_QueryPorts.install (FIp_Install.configuration err c r).query))).op20=FIp_DotsAdapter.dots ∧
    (Tx1Q_QueryBridge.leaves (FIp_Install.configuration err c r).query).op11=Port4B_Opening.opening ∧
    (Port3_QueryStage.release (Port4C_RowStd.install
      (Port5Q1_QueryPorts.install (FIp_Install.configuration err c r).query))).op11=Port4B_Opening.opening := ⟨rfl,rfl,rfl,rfl⟩
#print axioms installed
end AspisR1.FJl_SourceSlots
end
