import NIL_ResultTransport
set_option autoImplicit false
noncomputable section
namespace NIL_ResultReverse
open Aeneas Aeneas.Std Result NIL_Carriers

theorem inner_reverse {A B : Type} (f : A → B) (g : B → A)
 (law : ∀ x,g (f x)=x) (m : core.result.Result A Cohort.Err) :
 NIL_Carriers.inner g (unInner f m)=m := by
 cases m <;> simp only [NIL_Carriers.inner,unInner,law,error_reverse]

theorem bind_outer {A B C : Type} (f : A → B) (m : Result A) (next : B → Result C) :
 (do let x ← outer f m;next x)=(do let x ← m;next (f x)) := by cases m <;> rfl

theorem outer_if {A B : Type} (f : A → B) (b : Bool) (x y : Result A) :
 outer f (if b then x else y)=(if b then outer f x else outer f y) := by cases b <;> rfl

theorem outer_fail_iff {A B : Type} (f : A → B) (m : Result A) (err : Error) :
 outer f m=fail err ↔ m=fail err := by cases m <;> simp [outer]

theorem outer_div_iff {A B : Type} (f : A → B) (m : Result A) :
 outer f m=div ↔ m=div := by cases m <;> simp [outer]
#print axioms inner_reverse
#print axioms bind_outer
#print axioms outer_if
#print axioms outer_fail_iff
#print axioms outer_div_iff
end NIL_ResultReverse
