import RPz7_Op5T_Final
import RPz7_Tx1Q_Endpoint
import RPz7_Op4P_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.Uni_Install

/-- The base given to Op5T: scan and all TX1 prefix slots are fixed. -/
def base {C : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C) :=
  Op4P_Install.install (Tx1Q_Execution.base ops reserved query geo)

def current {C : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C) :=
  Op3I_Install.install (Op5T_Concrete.current (base ops reserved query geo))

/-- Exact dictionary equality, not a compatibility hypothesis. -/
theorem compose_tx1 {C : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C) :
    current ops reserved query geo =
      Tx1Q_SameCut.dictionary (Op5T_Concrete.current ops) reserved query geo := by
  cases ops; rfl

/-- Scan and batch occupy disjoint slots. -/
theorem scan_batch (ops : AspisR1CurrentCaller.Ops) :
    Op5T_Concrete.current (Op4P_Install.install ops) =
      Op4P_Install.install (Op5T_Concrete.current ops) := by
  cases ops; rfl

/-- Every TX1 prefix slot is disjoint from batch. -/
theorem prefix_batch {C : Type} (ops : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C) :
    Op5T_Concrete.current (Tx1Q_Execution.base ops reserved query geo) =
      Tx1Q_Execution.base (Op5T_Concrete.current ops) reserved query geo := by
  cases ops; rfl

/-- Reapplying overlapping shape/scan installers agrees exactly. -/
theorem overlap (ops : AspisR1CurrentCaller.Ops) :
    Op3I_Install.install (Op4P_Install.install
      (Op3I_Install.install (Op4P_Install.install ops))) =
    Op3I_Install.install (Op4P_Install.install ops) := by
  cases ops; rfl

#print axioms compose_tx1
#print axioms scan_batch
#print axioms prefix_batch
#print axioms overlap
end AspisR1.Uni_Install
end
