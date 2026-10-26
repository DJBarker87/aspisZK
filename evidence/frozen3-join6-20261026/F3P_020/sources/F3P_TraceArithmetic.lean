import AspisR1DecodeKFullSuccessIndexedParser
set_option autoImplicit false
namespace AspisR1.F3P_TraceArithmetic
open Aeneas Aeneas.Std Result

theorem checked_add (x y z : Usize) (h : x+y=ok z) : z.val=x.val+y.val := by
  have bound : x.val+y.val≤UScalar.max .Usize := by scalar_tac
  have spec := UScalar.add_spec (x:=x) (y:=y) bound
  rw [h] at spec
  exact spec

theorem checked_mul (x y z : Usize) (h : x*y=ok z) : z.val=x.val*y.val := by
  have bound : x.val*y.val≤UScalar.max .Usize := by scalar_tac
  have spec := UScalar.mul_spec (x:=x) (y:=y) bound
  rw [h] at spec
  exact spec

#print axioms checked_add
#print axioms checked_mul
end AspisR1.F3P_TraceArithmetic
