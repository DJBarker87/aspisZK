import FIv_Arithmetic
set_option autoImplicit false
namespace AspisR1.FIw_WordValue
open Aeneas Aeneas.Std Result

theorem mul {ty : UScalarTy} (x y out : UScalar ty) (run : x*y=ok out) :
    out.val=x.val*y.val := by
  have h := UScalar.tryMk_eq ty (x.val*y.val)
  change UScalar.tryMk ty (x.val*y.val)=ok out at run
  rw [run] at h
  exact h.1

theorem add {ty : UScalarTy} (x y out : UScalar ty) (run : x+y=ok out) :
    out.val=x.val+y.val := by
  have h := UScalar.tryMk_eq ty (x.val+y.val)
  change UScalar.tryMk ty (x.val+y.val)=ok out at run
  rw [run] at h
  exact h.1
#print axioms mul
#print axioms add
end AspisR1.FIw_WordValue
