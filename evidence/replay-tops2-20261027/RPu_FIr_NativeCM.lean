import RPu_FIr_NativeArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_NativeCM
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (map map_bind map_ok)
open FIr_NativeArithmetic

theorem add (x y : NC) : map cm (FIq_Native.field.CM31.add x y)=
    AspisR1SelectedMaskProbe.field.CM31.add (cm x) (cm y) := by
  simp only [FIq_Native.field.CM31.add,AspisR1SelectedMaskProbe.field.CM31.add,
    cm,map_bind,map_ok,m31_add]

theorem sub (x y : NC) : map cm (FIq_Native.field.CM31.sub x y)=
    AspisR1SelectedMaskProbe.field.CM31.sub (cm x) (cm y) := by
  simp only [FIq_Native.field.CM31.sub,AspisR1SelectedMaskProbe.field.CM31.sub,
    cm,map_bind,map_ok,m31_sub]

theorem mul (x y : NC) : map cm (FIq_Native.field.CM31.mul x y)=
    AspisR1SelectedMaskProbe.field.CM31.mul (cm x) (cm y) := by
  simp only [FIq_Native.field.CM31.mul,AspisR1SelectedMaskProbe.field.CM31.mul,
    cm,map_bind,map_ok,m31_mul,m31_sub,m31_reduce]

theorem by_r (x : NC) : map cm (FIq_Native.field.mul_by_r x)=
    AspisR1SelectedMaskProbe.field.mul_by_r (cm x) := by
  simp only [FIq_Native.field.mul_by_r,AspisR1SelectedMaskProbe.field.mul_by_r,
    FIq_Native.field.M31.double,AspisR1SelectedMaskProbe.field.M31.double,
    cm,map_bind,map_ok,m31_add,m31_sub]

#print axioms add
#print axioms sub
#print axioms mul
#print axioms by_r
end AspisR1.FIr_NativeCM
end
