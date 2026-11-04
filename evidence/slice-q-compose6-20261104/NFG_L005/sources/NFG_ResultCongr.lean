import Aeneas.Std
set_option autoImplicit false
namespace NFG_ResultCongr
open Aeneas Aeneas.Std Result

/-- Extensional congruence preserves ok, fail and div without importing a generated forest. -/
theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (same : ∀ x, f x = g x) : (r >>= f) = (r >>= g) := by
  cases r with
  | fail => rfl
  | div => rfl
  | ok x => exact same x

theorem right {A : Type} (r : Result A) : (do let x ← r; ok x) = r := by
  cases r <;> rfl

theorem split {A B C : Type} (f : A → B → C) (p : A × B) :
    (match p with | (a,b) => f a b) = f p.1 p.2 := by
  cases p; rfl

theorem pair_bind {A B C : Type} (r : Result (A × B)) (f : A → B → Result C) :
    (do let (a,b) ← r; f a b) = (do let p ← r; f p.1 p.2) := by
  cases r with
  | fail => rfl
  | div => rfl
  | ok p => cases p; rfl

#print axioms bind_congr
#print axioms right
#print axioms split
#print axioms pair_bind
end NFG_ResultCongr
