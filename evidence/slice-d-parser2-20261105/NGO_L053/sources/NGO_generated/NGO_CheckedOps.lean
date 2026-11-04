import NGD_DecodeEntry
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_CheckedOps
#print core.num.checked_mul_UScalar
#print core.num.checked_add_UScalar
theorem mul (x y z : Usize) (equation : x.val*y.val=z.val) :
    Usize.checked_mul x y=some z := by
  have bounded : x.val*y.val≤Usize.max := by rw [equation];exact z.hmax
  simp only [Usize.checked_mul,core.num.checked_mul_UScalar]
  trace_state
  split
  · congr 1;apply UScalar.eq_of_val_eq;exact equation
  · contradiction

theorem add (x y z : Usize) (equation : x.val+y.val=z.val) :
    Usize.checked_add x y=some z := by
  have bounded : x.val+y.val≤Usize.max := by rw [equation];exact z.hmax
  simp only [Usize.checked_add,core.num.checked_add_UScalar]
  trace_state
  split
  · congr 1;apply UScalar.eq_of_val_eq;exact equation
  · contradiction
#print axioms mul
#print axioms add
end NGO_CheckedOps
