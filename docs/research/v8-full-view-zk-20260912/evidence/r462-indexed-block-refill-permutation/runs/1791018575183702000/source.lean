import AspisV8R19.R456IndexedWordPermutation
import AspisV8R19.R451BlockStoppingCore

set_option autoImplicit false
namespace AspisV8R19.R461OptionScanCount
open AspisV8R19.R451BlockStoppingPermutation
open AspisV8R19.R442RejectionAlphabet
open AspisV8R19.R456IndexedWordPermutation

def optionCount {p : Nat} : List (Option (Fin p)) → Nat
  | [] => 0
  | none :: xs => optionCount xs + 1
  | some _ :: _ => 1

theorem transform_optionCount {p : Nat}
    (σ : Nat → Equiv.Perm (Fin p)) (offset : Nat)
    (xs : List (Option (Fin p))) :
    optionCount (transform σ offset xs) = optionCount xs := by
  induction xs generalizing offset with
  | nil => rfl
  | cons head xs ih =>
      cases head with
      | none => simp [transform, optionCount, ih]
      | some a => rfl

theorem countScan_map_val_eq_optionCount {p : Nat}
    (ws : List (Fin (p + 1))) :
    countScan p (ws.map Fin.val) =
      optionCount (ws.map (alphabetDecode p)) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      by_cases hp : w.val = p
      · have hnot : ¬ w.val < p := by omega
        simp [countScan, optionCount, alphabetDecode, hp, hnot, ih]
      · have hlt : w.val < p := by omega
        simp [countScan, optionCount, alphabetDecode, hp, hlt]

#print axioms transform_optionCount
#print axioms countScan_map_val_eq_optionCount
end AspisV8R19.R461OptionScanCount
