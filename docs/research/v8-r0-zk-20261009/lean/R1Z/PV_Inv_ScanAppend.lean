import R1Z.PV_Inv_Scan
set_option autoImplicit false
namespace R1Z.PV_Inv_ScanAppend
open PV_Inv_Scan
variable {K : Type} [DecidableEq K]

theorem append (chi : K) (xs ys : List K) (clear : Bool) :
    scan chi clear (xs++ys) = scan chi (scan chi clear xs) ys := by
  induction xs generalizing clear with
  | nil => rfl
  | cons x xs ih => exact ih (clear && decide (chi ≠ x))

theorem false_sticky (chi : K) (xs : List K) : scan chi false xs = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [scan] using ih

theorem prefix_clear (chi : K) (xs ys : List K) (h : scan chi true (xs++ys)=true) :
    scan chi true xs=true := by
  rw [append] at h
  exact ((scan_iff chi (scan chi true xs) ys).mp h).1

#print axioms append
#print axioms false_sticky
#print axioms prefix_clear
end R1Z.PV_Inv_ScanAppend
