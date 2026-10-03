import AspisV8R19.R449BlockPermutation

set_option autoImplicit false
namespace AspisV8R19.R456IndexedWordPermutation

/-- Apply a position-specific permutation to each accepted tape entry while
leaving rejection markers in place. -/
def transform {p : Nat} (σ : Nat → Equiv.Perm (Fin p)) :
    Nat → List (Option (Fin p)) → List (Option (Fin p))
  | _, [] => []
  | offset, none :: xs => none :: transform σ offset xs
  | offset, some a :: xs => some (σ offset a) :: transform σ (offset + 1) xs

theorem transform_inverse_left {p : Nat} (σ : Nat → Equiv.Perm (Fin p))
    (offset : Nat) (xs : List (Option (Fin p))) :
    transform (fun i => (σ i).symm) offset (transform σ offset xs) = xs := by
  induction xs generalizing offset with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | none => simp [transform, ih]
      | some a => simp [transform, ih]

theorem transform_inverse_right {p : Nat} (σ : Nat → Equiv.Perm (Fin p))
    (offset : Nat) (xs : List (Option (Fin p))) :
    transform σ offset (transform (fun i => (σ i).symm) offset xs) = xs := by
  induction xs generalizing offset with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | none => simp [transform, ih]
      | some a => simp [transform, ih]

def indexedTapeEquiv {p : Nat} (σ : Nat → Equiv.Perm (Fin p)) (offset : Nat) :
    List (Option (Fin p)) ≃ List (Option (Fin p)) where
  toFun := transform σ offset
  invFun := transform (fun i => (σ i).symm) offset
  left_inv := transform_inverse_left σ offset
  right_inv := transform_inverse_right σ offset

theorem transform_length {p : Nat} (σ : Nat → Equiv.Perm (Fin p))
    (offset : Nat) (xs : List (Option (Fin p))) :
    (transform σ offset xs).length = xs.length := by
  induction xs generalizing offset with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [transform, ih]

theorem transform_isSome_count {p : Nat} (σ : Nat → Equiv.Perm (Fin p))
    (offset : Nat) (xs : List (Option (Fin p))) :
    ((transform σ offset xs).filter Option.isSome).length =
      (xs.filter Option.isSome).length := by
  induction xs generalizing offset with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [transform, ih]

theorem transform_status {p : Nat} (σ : Nat → Equiv.Perm (Fin p))
    (offset : Nat) (xs : List (Option (Fin p))) :
    (transform σ offset xs).map Option.isSome = xs.map Option.isSome := by
  induction xs generalizing offset with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [transform, ih]

#print axioms transform_inverse_left
#print axioms transform_inverse_right
#print axioms indexedTapeEquiv
#print axioms transform_length
#print axioms transform_isSome_count
#print axioms transform_status

end AspisV8R19.R456IndexedWordPermutation
