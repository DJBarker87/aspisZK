import FJa_SquareValue
import FIo_M31Values
set_option autoImplicit false
namespace AspisR1.FJm_MaskScalarBridge
open Aeneas Aeneas.Std Result

theorem reduce (x : U64) : FIo_Native.aspis_core.field.M31.reduce_u64 x=
    AspisR1SelectedMaskProbe.field.M31.reduce_u64 x := by
  simp only [FIo_Native.aspis_core.field.M31.reduce_u64,
    AspisR1SelectedMaskProbe.field.M31.reduce_u64,FIo_ReduceBridge.same,
    AspisR1CurrentWide.Proof.reduce_same]
  rfl

theorem mul (x y : U32) : FIo_Native.aspis_core.field.M31.mul x y=
    AspisR1SelectedMaskProbe.field.M31.mul x y := by
  rw [FIo_M31MulBridge.same,AspisR1CurrentWide.Proof.m31_mul_same]
  rfl

theorem add (x y : U32) (hx : x.val<2147483647) (hy : y.val<2147483647) :
    FIo_Native.aspis_core.field.M31.add x y=AspisR1SelectedMaskProbe.field.M31.add x y := by
  rw [FIo_M31Bridge.add x y hx hy,AspisR1CurrentWide.Proof.m31_add_same]
  rfl
#print axioms reduce
#print axioms mul
#print axioms add
end AspisR1.FJm_MaskScalarBridge
