import NEB_MulReducerCall
import NEB_CMCarrier
import FIo_ScalarBridge
set_option autoImplicit false
namespace NEB_NativeFieldScalars
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem size64 : UScalar.size .U64=18446744073709551616 := by
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]

theorem m31_checked_product (x y : U32) :
    (UScalar.cast .U64 x)*(UScalar.cast .U64 y)=ok (NEB_MulReducerCall.product x y) := by
  apply FIo_ScalarBridge.mul
  have xv : (UScalar.cast .U64 x).val=x.val := by scalar_tac
  have yv : (UScalar.cast .U64 y).val=y.val := by scalar_tac
  rw [xv,yv,size64]
  exact LPf_BaseMultiply.product_bound x y

theorem sum_checked (x : NC) :
    (core.convert.num.FromU64U32.from x.a)+(core.convert.num.FromU64U32.from x.b)=
      ok (LPi_CMProduct.sum x) := by
  apply FIo_ScalarBridge.add
  rw [NEB_CMCarrier.lossless,NEB_CMCarrier.lossless,size64]
  have a : x.a.val<4294967296 := by scalar_tac
  have b : x.b.val<4294967296 := by scalar_tac
  change x.a.val+x.b.val<18446744073709551616
  omega

/-- This is the checked scalar expression in the ACTUAL frozen caller; its
sums and product equal the emitted raw recurrence input without overflow. -/
theorem cross_checked (x y : NC) (hx : canonC x) (hy : canonC y) :
    (do
      let a ← (core.convert.num.FromU64U32.from x.a)+(core.convert.num.FromU64U32.from x.b)
      let b ← (core.convert.num.FromU64U32.from y.a)+(core.convert.num.FromU64U32.from y.b)
      a*b)=ok (LPi_CMProduct.cross x y) := by
  rw [sum_checked x,sum_checked y]
  simp only [bind_tc_ok]
  apply FIo_ScalarBridge.mul
  rw [LPi_CMProduct.sum_value,LPi_CMProduct.sum_value,size64]
  have a : x.a.val+x.b.val<4294967296 := by rcases hx with ⟨_,_⟩;omega
  have b : y.a.val+y.b.val<4294967296 := by rcases hy with ⟨_,_⟩;omega
  exact Nat.mul_lt_mul_of_lt_of_lt a b

#print axioms size64
#print axioms m31_checked_product
#print axioms sum_checked
#print axioms cross_checked
end NEB_NativeFieldScalars
