import LPk_Step
set_option autoImplicit false
namespace NDH_Cast
open Aeneas Aeneas.Std
open AspisR1.SamplerMachineBounds

theorem cohort_cast (x : U64) (hx : x.val < B) :
    (UScalar.cast .U32 x).val = x.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt hx
#print axioms cohort_cast
end NDH_Cast
