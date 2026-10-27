import PV_B1_Transport
set_option autoImplicit false
noncomputable section
namespace PV_B1_ResultFaithful
open Aeneas Aeneas.Std Result PV_B1_Transport
theorem injective {A B : Type} (f : A → B) (g : B → A) (inv : ∀ a, g (f a)=a)
    (a b : Result A) (h : resultMap f a=resultMap f b) : a=b := by
  have h1 := congrArg (resultMap g) h
  simpa only [result_roundtrip f g inv] using h1

theorem failure_iff {A B : Type} (f : A → B) (r : Result A) (e : Error) :
    resultMap f r=fail e ↔ r=fail e := by cases r <;> simp only [resultMap,Result.noConfusion,Result.fail.injEq]
theorem divergence_iff {A B : Type} (f : A → B) (r : Result A) :
    resultMap f r=div ↔ r=div := by cases r <;> simp only [resultMap,Result.noConfusion]
#print axioms injective
#print axioms failure_iff
#print axioms divergence_iff
end PV_B1_ResultFaithful
