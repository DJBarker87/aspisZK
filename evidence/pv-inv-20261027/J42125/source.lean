import R1Z.PV_Inv_ScanAppend
set_option autoImplicit false
namespace R1Z.PV_Inv_ScanMask
open PV_Inv_Scan
variable {K : Type} [DecidableEq K]

def scanRows (chi : K) : Bool → List (Bool × List K) → Bool
  | c,[] => c
  | c,(active,xs)::rs => scanRows chi (if active then scan chi c xs else c) rs

theorem rows_iff (chi : K) (c : Bool) (rs : List (Bool × List K)) :
    scanRows chi c rs=true ↔ c=true ∧ ∀ r ∈ rs, r.1=true → ∀ x ∈ r.2, chi ≠ x := by
  induction rs generalizing c with
  | nil => simp [scanRows]
  | cons r rs ih =>
    rcases r with ⟨a,xs⟩
    cases a <;> simp [scanRows,ih,scan_iff,and_assoc]

#print axioms rows_iff
end R1Z.PV_Inv_ScanMask
