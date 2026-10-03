import AspisV8R19.R456IndexedWordPermutation
import AspisV8R19.R457IndexedScan

set_option autoImplicit false
namespace AspisV8R19.R465AllAcceptedPermutation
open AspisV8R19.R456IndexedWordPermutation

def acceptedValues {p : Nat} : List (Option (Fin p)) → List (Fin p)
  | [] => []
  | none :: xs => acceptedValues xs
  | some a :: xs => a :: acceptedValues xs

def permuteAccepted {p : Nat} (σ : Nat → Equiv.Perm (Fin p)) :
    Nat → List (Fin p) → List (Fin p)
  | _, [] => []
  | offset, a :: xs => σ offset a :: permuteAccepted σ (offset + 1) xs

theorem acceptedValues_transform {p : Nat}
    (σ : Nat → Equiv.Perm (Fin p)) (offset : Nat)
    (xs : List (Option (Fin p))) :
    acceptedValues (transform σ offset xs) =
      permuteAccepted σ offset (acceptedValues xs) := by
  induction xs generalizing offset with
  | nil => rfl
  | cons head xs ih =>
      cases head with
      | none => simpa [transform, acceptedValues, permuteAccepted] using ih offset
      | some a => simp [transform, acceptedValues, permuteAccepted, ih]

theorem permuteAccepted_length {p : Nat}
    (σ : Nat → Equiv.Perm (Fin p)) (offset : Nat)
    (xs : List (Fin p)) :
    (permuteAccepted σ offset xs).length = xs.length := by
  induction xs generalizing offset with
  | nil => rfl
  | cons a xs ih => simp [permuteAccepted, ih]

theorem acceptedValues_transform_length {p : Nat}
    (σ : Nat → Equiv.Perm (Fin p)) (offset : Nat)
    (xs : List (Option (Fin p))) :
    (acceptedValues (transform σ offset xs)).length = (acceptedValues xs).length := by
  rw [acceptedValues_transform, permuteAccepted_length]

#print axioms acceptedValues_transform
#print axioms permuteAccepted_length
#print axioms acceptedValues_transform_length
end AspisV8R19.R465AllAcceptedPermutation
