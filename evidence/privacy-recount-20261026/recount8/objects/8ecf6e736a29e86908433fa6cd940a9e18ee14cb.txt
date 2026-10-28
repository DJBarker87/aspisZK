import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ResultPost41
open Aeneas Aeneas.Std Result

def Post {A : Type} (p : A → Prop) : Result A → Prop
  | .ok a => p a
  | .fail _ | .div => True

theorem bind {A B : Type} (p : B → Prop) (r : Result A) (f : A → Result B)
    (good : ∀ a, Post p (f a)) : Post p (r >>= f) := by
  cases r with
  | ok a => exact good a
  | fail e => trivial
  | div => trivial

theorem success {A : Type} (p : A → Prop) (r : Result A) (a : A)
    (post : Post p r) (h : r=.ok a) : p a := by
  rw [h] at post
  exact post

/-- This direction only extracts successful bind components. It does not
project away failure/divergence from any execution or decoder. -/
theorem bind_success {A B : Type} (r : Result A) (f : A → Result B) (b : B)
    (h : (r >>= f)=.ok b) : ∃ a, r=.ok a ∧ f a=.ok b := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => cases h
  | div => cases h
#print axioms bind
#print axioms success
#print axioms bind_success
end R1Z.PV_RunJoin_ResultPost41
