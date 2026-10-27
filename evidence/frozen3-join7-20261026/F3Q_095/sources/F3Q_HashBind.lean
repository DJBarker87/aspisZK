import AuS1_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_HashBind
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.PreparedHashCode

theorem run_ok {A B : Type} (p : Code A) (k : A → Code B) (a : A) (success : erase p=ok a) :
    run (AspisR1PublicPreparation.PreparedHashCode.bind p k)=((run p).1++(run (k a)).1,(run (k a)).2) := by
  change run (AspisR1PublicPreparation.PreparedHashCode.bind p k)=_
  rw [AuS1_Trace.run_bind,run_value,success]
  rfl

theorem lift_run {A : Type} (r : Result A) : run (monadLift r : Code A)=([],r) := by
  cases r <;> rfl

#print axioms run_ok
#print axioms lift_run
end AspisR1.F3Q_HashBind
end
