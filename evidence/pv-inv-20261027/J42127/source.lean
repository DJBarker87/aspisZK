import R1Z.PV_Inv_ScanMask
set_option autoImplicit false
namespace R1Z.PV_Inv_ScanCost
open PV_Inv_Scan
variable {K : Type} [DecidableEq K]

/-- One event per compared slot, including comparisons after an earlier pole. -/
def recorded (chi : K) : Bool → List K → Bool × List Bool
  | c,[] => (c,[])
  | c,x::xs =>
    let result := recorded chi (c && decide (chi ≠ x)) xs
    (result.1,decide (chi ≠ x)::result.2)

theorem erases (chi : K) (c : Bool) (xs : List K) : (recorded chi c xs).1=scan chi c xs := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => exact ih _

theorem length (chi : K) (c : Bool) (xs : List K) : (recorded chi c xs).2.length=xs.length := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simpa [recorded] using congrArg Nat.succ (ih (c && decide (chi ≠ x)))

theorem safe_values (chi : K) (c : Bool) (xs : List K) (h : scan chi c xs=true) :
    (recorded chi c xs).2 = List.replicate xs.length true := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih =>
    have hx := ((scan_iff chi c (x::xs)).mp h).2 x (by simp)
    simp only [recorded]
    rw [ih _ h]
    simp [hx,List.replicate_succ]

#print axioms erases
#print axioms length
#print axioms safe_values
end R1Z.PV_Inv_ScanCost
