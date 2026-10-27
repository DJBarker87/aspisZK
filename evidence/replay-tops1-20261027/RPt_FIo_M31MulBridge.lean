import RPt_FIo_ReduceBridge
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIo_M31MulBridge
open Aeneas Aeneas.Std Result

theorem product_bound (x y : U32) :
    (UScalar.cast .U64 x).val*(UScalar.cast .U64 y).val<UScalar.size .U64 := by
  have cx : (UScalar.cast .U64 x).val=x.val := by scalar_tac
  have cy : (UScalar.cast .U64 y).val=y.val := by scalar_tac
  have hx : x.val≤4294967295 := by scalar_tac
  have hy : y.val≤4294967295 := by scalar_tac
  have hp := Nat.mul_le_mul hx hy
  rw [cx,cy]
  scalar_tac

theorem same (x y : U32) :
    FIo_Native.aspis_core.field.M31.mul x y=AspisR1CurrentWide.field.M31.mul x y := by
  have hm := FIo_ScalarBridge.mul (UScalar.cast .U64 x) (UScalar.cast .U64 y) (product_bound x y)
  simp only [FIo_Native.aspis_core.field.M31.mul,AspisR1CurrentWide.field.M31.mul,
    lift,bind_tc_ok,hm,FIo_ReduceBridge.same]
  rfl

#print axioms product_bound
#print axioms same
end AspisR1.FIo_M31MulBridge
end
