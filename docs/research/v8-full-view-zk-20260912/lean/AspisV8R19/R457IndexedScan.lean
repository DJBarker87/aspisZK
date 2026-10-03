import AspisV8R19.R456IndexedWordPermutation

set_option autoImplicit false
namespace AspisV8R19.R457IndexedScan
open R442RejectionAlphabet R456IndexedWordPermutation

theorem firstAccepted_transform {p : Nat} (σ : Nat → Equiv.Perm (Fin p))
    (offset : Nat) (xs : List (Option (Fin p))) :
    firstAccepted (transform σ offset xs) =
      Option.map (σ offset) (firstAccepted xs) := by
  induction xs generalizing offset with
  | nil => rfl
  | cons x xs ih =>
      cases x with
      | none => exact ih offset
      | some a => rfl

def acceptedCount {p : Nat} (xs : List (Option (Fin p))) : Nat :=
  (xs.filter Option.isSome).length

theorem transform_drop {p : Nat} (σ : Nat → Equiv.Perm (Fin p))
    (offset k : Nat) (xs : List (Option (Fin p))) :
    (transform σ offset xs).drop k =
      transform σ (offset + acceptedCount (xs.take k)) (xs.drop k) := by
  induction k generalizing offset xs with
  | zero => simp [acceptedCount]
  | succ k ih =>
      cases xs with
      | nil => simp [transform, acceptedCount]
      | cons x xs =>
          cases x with
          | none => simpa [transform, acceptedCount] using ih offset xs
          | some a =>
              simpa [transform, acceptedCount, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using ih (offset+1) xs

#print axioms firstAccepted_transform
#print axioms transform_drop
end AspisV8R19.R457IndexedScan
