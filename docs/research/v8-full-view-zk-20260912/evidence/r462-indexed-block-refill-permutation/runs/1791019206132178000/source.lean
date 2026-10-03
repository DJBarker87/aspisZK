import AspisV8R19.R457IndexedScan
import AspisV8R19.R461OptionScanCount

set_option autoImplicit false
namespace AspisV8R19.R463ConsumedAcceptanceCount
open AspisV8R19.R442RejectionAlphabet
open AspisV8R19.R457IndexedScan
open AspisV8R19.R461OptionScanCount
open AspisV8R19.R456IndexedWordPermutation

theorem acceptedCount_take_optionCount {p : Nat}
    (xs : List (Option (Fin p))) :
    acceptedCount (xs.take (optionCount xs)) =
      if (firstAccepted xs).isSome then 1 else 0 := by
  induction xs with
  | nil => rfl
  | cons head xs ih =>
      cases head with
      | none =>
          have ht : (none :: xs).take (optionCount xs + 1) =
              none :: xs.take (optionCount xs) := by simp
          rw [show optionCount (none :: xs) = optionCount xs + 1 by rfl, ht]
          simp only [acceptedCount, List.filter_cons, Option.isSome_none,
            Bool.false_eq_true, ite_false, List.length_cons]
          rw [ih]
          simp [firstAccepted]
      | some a =>
          simp [optionCount, firstAccepted, acceptedCount]

theorem transform_drop_optionCount {p : Nat}
    (σ : Nat → Equiv.Perm (Fin p)) (offset : Nat)
    (xs : List (Option (Fin p))) :
    (transform σ offset xs).drop (optionCount xs) =
      transform σ (offset + (if (firstAccepted xs).isSome then 1 else 0))
        (xs.drop (optionCount xs)) := by
  rw [transform_drop, acceptedCount_take_optionCount]

#print axioms acceptedCount_take_optionCount
#print axioms transform_drop_optionCount
end AspisV8R19.R463ConsumedAcceptanceCount
