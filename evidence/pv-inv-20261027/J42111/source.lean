import R1Z.PV_Inv_Guard
import Mathlib.Data.List.Basic
set_option autoImplicit false
namespace R1Z.PV_Inv_Scan
variable {K : Type} [DecidableEq K]

def scan (chi : K) : Bool → List K → Bool
  | clear,[] => clear
  | clear,x::xs => scan chi (clear && decide (chi ≠ x)) xs

theorem scan_iff (chi : K) (clear : Bool) (xs : List K) :
    scan chi clear xs = true ↔ clear = true ∧ ∀ x ∈ xs, chi ≠ x := by
  induction xs generalizing clear with
  | nil => simp [scan]
  | cons x xs ih => simp [scan,ih,and_assoc]

theorem scan_nonzero {K : Type} [Field K] [DecidableEq K]
    (chi : K) (xs : List K) (h : scan chi true xs = true) :
    ∀ x ∈ xs, chi-x ≠ 0 := by
  intro x hx
  exact sub_ne_zero.mpr ((scan_iff chi true xs).mp h).2 x hx

#print axioms scan_iff
#print axioms scan_nonzero
end R1Z.PV_Inv_Scan
