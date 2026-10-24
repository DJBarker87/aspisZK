import S1PreparedCodeLawsV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.PreparedHashCode
open Aeneas Aeneas.Std Result

theorem code_pair_bind_congr {A B C : Type} (p : Code (A × B))
    (f g : A → B → Code C) (h : ∀ a b, f a b=g a b) :
    (do let (a,b) ← p; f a b)=(do let (a,b) ← p; g a b) := by
  apply congrArg (fun next => p >>= next)
  funext pair
  cases pair with
  | mk a b => exact h a b

#print axioms code_pair_bind_congr
end AspisR1PublicPreparation.PreparedHashCode
