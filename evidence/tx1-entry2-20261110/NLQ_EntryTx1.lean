import NLQ_DispatchTx1
set_option autoImplicit false
noncomputable section
namespace NLQ_EntryTx1
open Aeneas Aeneas.Std Result AspisR1 NLQ_DispatchState
/-- Admission is computed from the original data. No Bool outcome is a root
premise; the complete state and child error/abort prefix are then forwarded. -/
theorem admitted_ten : Hiq_DispatchSource.pool_route.admitted NJD_Prefixes.ten=.ok true := by
 rfl
theorem admitted_eleven : Hiq_DispatchSource.pool_route.admitted NJD_Prefixes.eleven=.ok true := by
 rfl
theorem admitted (d : Slice U8) (tx1 : NLQ_Route.Tx1 d) :
 Hiq_DispatchSource.pool_route.admitted d=.ok true := by
 rcases tx1 with h | h
 · have eq : d=NJD_Prefixes.ten := Subtype.ext h
   subst d; exact admitted_ten
 · have eq : d=NJD_Prefixes.eleven := Subtype.ext h
   subst d; exact admitted_eleven
theorem fold {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F) (tx1 : NLQ_Route.Tx1 d) :
 entry children p a d world =
 prepend [.admitted world d (.ok true)] (process children p a d world) := by
 simp only [entry,admitted d tx1,step,ite_true]
theorem complete {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F) (tx1 : NLQ_Route.Tx1 d) :
 ((entry children p a d world).result,(entry children p a d world).post)=
 ((children.first p a d world).result,(children.first p a d world).post) := by
 rw [fold children p a d world tx1]
 exact NLQ_DispatchTx1.complete children p a d world tx1
#print fold
#print complete
#print axioms admitted_ten
#print axioms admitted_eleven
#print axioms admitted
#print axioms fold
#print axioms complete
end NLQ_EntryTx1
