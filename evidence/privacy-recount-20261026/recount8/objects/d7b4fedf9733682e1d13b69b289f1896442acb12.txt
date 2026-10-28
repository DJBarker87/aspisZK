import R1Z.ProverRwP6BodyStore
set_option autoImplicit false
namespace R1Z.ProverRwP6ResultMap
open Aeneas Aeneas.Std Result
abbrev map {A B : Type} := @ProverRwDictionaryTower.mapResult A B
theorem compose {A B C : Type} (f : A → B) (g : B → C) (r : Result A) :
    map g (map f r) = map (g ∘ f) r := by cases r <;> rfl
theorem bind {A B C : Type} (f : B → C) (r : Result A) (next : A → Result B) :
    map f (do let a ← r; next a) = (do let a ← r; map f (next a)) := by
  cases r <;> rfl
theorem roundtrip {A B : Type} (f : A → B) (g : B → A)
    (inverse : ∀ a, g (f a) = a) (r : Result A) : map g (map f r) = r := by
  cases r with
  | ok a => exact congrArg Result.ok (inverse a)
  | fail e => rfl
  | div => rfl
#print axioms compose
#print axioms bind
#print axioms roundtrip
end R1Z.ProverRwP6ResultMap
