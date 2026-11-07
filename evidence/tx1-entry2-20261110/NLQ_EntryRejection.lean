import NLQ_DispatchState
set_option autoImplicit false
noncomputable section
namespace NLQ_EntryRejection
open Aeneas Aeneas.Std Result AspisR1 NLQ_DispatchState
/-- Local branch lemma: the actual computed admission returns false. No
account inspection, borrow, child event, state mutation or suffix occurs. -/
theorem rejected {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F)
 (branch : Hiq_DispatchSource.pool_route.admitted d=.ok false) :
 entry children p a d world =
 ⟨.ok (.Err .InvalidInstructionData),world,[.admitted world d (.ok false)]⟩ := by
 simp [entry,branch,step,prepend]
/-- Full outer error prefix is retained; no successful admission is assumed. -/
theorem fail {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F) (e : Error)
 (branch : Hiq_DispatchSource.pool_route.admitted d=.fail e) :
 entry children p a d world = ⟨.fail e,world,[.admitted world d (.fail e)]⟩ := by
 simp only [entry,branch,step]
theorem div {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F)
 (branch : Hiq_DispatchSource.pool_route.admitted d=.div) :
 entry children p a d world = ⟨.div,world,[.admitted world d .div]⟩ := by
 simp only [entry,branch,step]
#print rejected
#print axioms rejected
#print axioms fail
#print axioms div
end NLQ_EntryRejection
