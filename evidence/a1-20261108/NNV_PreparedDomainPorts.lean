import NNV_PreparedInputs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNV_PreparedDomainPorts
open Aeneas Aeneas.Std Result NNV_PreparedInputs
/-- The input-domain record refers to the SAME Verified/View/scratch as the
native port theorem, including its original Expanded and semantic provenance. -/
theorem input (s : RSL.Verified LIB_VLib.library) (v : LIB_VCarriers.View) (g : LIB_VCarriers.E29) :
 (AspisR1CurrentCaller.InstalledPreparation.retainedSem (sem s),
  AspisR1CurrentCaller.InstalledPreparation.retainedView (view v),
  AspisR1ClaimPreparedBridge.mapArray AspisR1CurrentCaller.InstalledPreparation.retainedE (scratch g)) =
 LIB_Prepared.input (s,v,g) := by
 rw [semantic,view_input,scratch_input]
 rfl

theorem domain (s : RSL.Verified LIB_VLib.library) (v : LIB_VCarriers.View) (g : LIB_VCarriers.E29)
 (established : LIB_Prepared.child.dom (s,v,g)) :
 LIBC_PreparedDomain.Domain
 (AspisR1CurrentCaller.InstalledPreparation.retainedSem (sem s),
  AspisR1CurrentCaller.InstalledPreparation.retainedView (view v),
  AspisR1ClaimPreparedBridge.mapArray AspisR1CurrentCaller.InstalledPreparation.retainedE (scratch g)) := by
 rw [input]
 exact (LIB_Prepared.caller_clauses _).mp established
#print axioms input
#print axioms domain
end AspisR1.NNV_PreparedDomainPorts
end
