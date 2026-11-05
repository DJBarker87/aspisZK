import NHS_ContextQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_QueryIdentity
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody
/-- The current bridge leaves the line callback abstract. -/
theorem leaves_line (ops : Ops) :
 (Tx1Q_QueryBridge.leaves ops).op16=ops.op16 := rfl
/-- NFS replaces this same callback with the closed line implementation. -/
theorem installed_line (ops : Ops) :
 (NFS_QueryOps.installed ops).op16=SAQ_LineQuery.line := rfl
/-- An exact dictionary identification requires an additional primitive law.
This is a necessary condition, not a new assumption used to book a row. -/
theorem necessary (ops base : Ops)
 (same : Tx1Q_QueryBridge.leaves ops=NFS_QueryOps.installed base) :
 ops.op16=SAQ_LineQuery.line := by
 have h := congrArg (fun d : Ops => d.op16) same
 exact h
#print axioms leaves_line
#print axioms installed_line
#print axioms necessary
end AspisR1.NHW_QueryIdentity
