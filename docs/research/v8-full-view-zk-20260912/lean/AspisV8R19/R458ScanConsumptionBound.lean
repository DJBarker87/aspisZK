import AspisV8R19.R444InitialSourceLimb

set_option autoImplicit false
namespace AspisV8R19.R458ScanConsumptionBound
open AspisV8R19.R444InitialSourceLimb

theorem sourceScan_count_le_length (ws : List Nat) :
    (sourceScan ws).2 ≤ ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      by_cases hw : w = 2147483647
      · simp [sourceScan, hw]
        omega
      · simp [sourceScan, hw]

theorem sourceScan_none_count_eq_length (ws : List Nat)
    (h : (sourceScan ws).1 = none) :
    (sourceScan ws).2 = ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      by_cases hw : w = 2147483647
      · have ht : (sourceScan ws).1 = none := by
          simpa [sourceScan, hw] using h
        simp only [sourceScan, if_pos hw, List.length_cons]
        rw [ih ht]
      · simp [sourceScan, hw] at h

theorem sourceScan_some_count_pos (ws : List Nat) (x : Nat)
    (h : (sourceScan ws).1 = some x) :
    0 < (sourceScan ws).2 := by
  induction ws with
  | nil => simp [sourceScan] at h
  | cons w ws ih =>
      by_cases hw : w = 2147483647
      · simp only [sourceScan, if_pos hw] at h ⊢
        exact Nat.succ_pos _
      · simp [sourceScan, hw] at h ⊢

#print axioms sourceScan_count_le_length
#print axioms sourceScan_none_count_eq_length
#print axioms sourceScan_some_count_pos
end AspisV8R19.R458ScanConsumptionBound
