import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9SourceResultTransportV1

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem mapResult_bind_eq {A B C D : Type}
    (g : A → B) (f : C → D) (source : Result A) (target : Result B)
    (sourceNext : A → Result C) (targetNext : B → Result D)
    (hfirst : mapResult g source = target)
    (hnext : ∀ x, mapResult f (sourceNext x) = targetNext (g x)) :
    mapResult f (source >>= sourceNext) = (target >>= targetNext) := by
  rw [← hfirst]
  cases source with
  | ok x => exact hnext x
  | fail e => rfl
  | div => rfl

theorem mapResult_eq_bind {A B : Type} (f : A → B) (r : Result A) :
    mapResult f r = (do let x ← r; ok (f x)) := by
  cases r <;> rfl

#print axioms mapResult_bind_eq
#print axioms mapResult_eq_bind
end AspisR1S9SourceResultTransportV1
