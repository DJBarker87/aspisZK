import AspisV8R19.R444InitialSourceLimb

set_option autoImplicit false
namespace AspisV8R19.R451BlockStoppingPermutation
open AspisV8R19.R444InitialSourceLimb

/-- Number of values consumed through the first non-sentinel entry. -/
def countScan (p : Nat) : List Nat → Nat
  | [] => 0
  | w :: ws => if w = p then countScan p ws + 1 else 1

theorem sourceScan_countScan (p : Nat) (ws : List Nat)
    (hp : p = 2147483647) :
    (sourceScan ws).2 = countScan p ws := by
  subst p
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      by_cases hw : w = 2147483647
      · simp [sourceScan, countScan, hw, ih]
      · simp [sourceScan, countScan, hw]

theorem countScan_perm_fix_sentinel (p : Nat)
    (e : Equiv.Perm (Fin (p + 1)))
    (he : e ⟨p, by omega⟩ = ⟨p, by omega⟩)
    (xs : List (Fin (p + 1))) :
    countScan p (xs.map Fin.val) =
      countScan p (xs.map fun x => (e x).val) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : (e x).val = p ↔ x.val = p := by
        constructor
        · intro h
          have hval : e x = ⟨p, by omega⟩ := Fin.ext h
          have heq : e x = e ⟨p, by omega⟩ := by rw [hval, he]
          exact congrArg Fin.val (e.injective heq)
        · intro h
          have hxval : x = ⟨p, by omega⟩ := Fin.ext h
          simpa [hxval, he]
      simp only [List.map_cons]
      simp [countScan, hx, ih]

theorem countScan_ofFn_perm {p n : Nat} (e : Equiv.Perm (Fin (p + 1)))
    (he : e ⟨p, by omega⟩ = ⟨p, by omega⟩)
    (xs : Fin n → Fin (p + 1)) :
    countScan p (List.ofFn (fun i => (xs i).val)) =
      countScan p (List.ofFn (fun i => (e (xs i)).val)) := by
  have h := countScan_perm_fix_sentinel p e he (List.ofFn xs)
  simpa only [List.map_ofFn, Function.comp_def] using h

#print axioms sourceScan_countScan
#print axioms countScan_perm_fix_sentinel
#print axioms countScan_ofFn_perm
end AspisV8R19.R451BlockStoppingPermutation
