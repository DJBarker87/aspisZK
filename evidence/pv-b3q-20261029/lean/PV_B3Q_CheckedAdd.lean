import PV_B3P_ClosureLinks14227
namespace PV_B3Q_CheckedAdd
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
/-- add_with_overflow's value interpretation; executing the intrinsic stays V370. -/
def overflow (x y : U64) : Bool := decide (UScalar.size .U64 ≤ x.val+y.val)
def add_with_overflow (x y : U64) : U64 × Bool := (U64.wrapping_add x y,overflow x y)
def unlikely (flag : Bool) : Bool := flag
/-- unlikely returns the same Bool; unchecked_add is called only in the nonoverflow
branch. Under that guard its value is precisely the wrapping sum. -/
def source (x y : U64) : Result (Option U64) :=
 if unlikely (add_with_overflow x y).2 then .ok none else .ok (some (U64.wrapping_add x y))
def model (x y : U64) : Result (Option U64) :=
 if x.val+y.val < UScalar.size .U64 then .ok (some (U64.wrapping_add x y)) else .ok none
theorem unchecked_precondition (x y : U64) (no_overflow : overflow x y = false) :
    x.val+y.val < UScalar.size .U64 := by
 simp only [overflow,decide_eq_false_iff_not,not_le] at no_overflow
 exact no_overflow
theorem unchecked_value (x y : U64) (no_overflow : overflow x y = false) :
    (U64.wrapping_add x y).val = x.val+y.val := by
 rw [U64.wrapping_add_val_eq,Nat.mod_eq_of_lt (unchecked_precondition x y no_overflow)]
theorem checked_add_link : PV_B3P_Link_std_dependency_closure14
    (fun _ : Unit => U64 → U64 → Result (Option U64)) (fun _ => source) (fun _ => model) := by
 intro _
 funext x y
 by_cases bound : x.val+y.val < UScalar.size .U64
 · have no_overflow : ¬UScalar.size .U64 ≤ x.val+y.val := by omega
   simp only [source,model,unlikely,add_with_overflow,overflow,no_overflow,bound,decide_false,Bool.false_eq_true,↓reduceIte]
 · have yes_overflow : UScalar.size .U64 ≤ x.val+y.val := by omega
   simp only [source,model,unlikely,add_with_overflow,overflow,yes_overflow,bound,decide_true,↓reduceIte]
#print axioms unchecked_precondition
#print axioms unchecked_value
#print axioms checked_add_link
end PV_B3Q_CheckedAdd
