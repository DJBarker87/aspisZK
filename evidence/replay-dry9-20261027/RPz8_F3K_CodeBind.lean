import RPz7_F3K_CodeStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_CodeBind
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode

theorem success {A B : Type} (m : Code A) (k : A → Code B) (v : A)
    (h : erase m=ok v) :
    observe (run (PreparedHashCode.bind m k)).1=
      observe (run m).1++observe (run (k v)).1 := by
  rw [AuS1_Trace.run_bind,run_value,h]
  exact AuS1_Trace.observe_append _ _

theorem pair_success {A B C : Type} (m : Code (A × B)) (k : A → B → Code C) (a : A) (b : B)
    (h : erase m=ok (a,b)) :
    observe (run (do let (x,y) ← m;k x y)).1=
      observe (run m).1++observe (run (k a b)).1 := by
  exact success m (fun xy=>k xy.1 xy.2) (a,b) h

theorem lifted_empty {A : Type} (m : Result A) : observe (run (monadLift m : Code A)).1=[] := by
  cases m <;> rfl

#print axioms success
#print axioms pair_success
#print axioms lifted_empty
end AspisR1.F3K_CodeBind
end
