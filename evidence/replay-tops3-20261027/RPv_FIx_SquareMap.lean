import RPv_FIv_SubMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_SquareMap
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic
open FIv_Map (map map_bind map_ok)

theorem cm_double (x : NC) : map cm (FIq_Native.field.CM31.double x)=
    AspisR1SelectedMaskProbe.field.CM31.double (cm x) := by
  unfold FIq_Native.field.CM31.double AspisR1SelectedMaskProbe.field.CM31.double
  exact FIv_NativeCM.add x x

theorem cm_square (x : NC) : map cm (FIq_Native.field.CM31.square x)=
    AspisR1SelectedMaskProbe.field.CM31.square (cm x) := by
  simp only [FIq_Native.field.CM31.square,AspisR1SelectedMaskProbe.field.CM31.square,
    FIq_Native.field.M31.double,AspisR1SelectedMaskProbe.field.M31.double,cm,map_bind,map_ok,m31_mul,m31_add,m31_sub,m31_reduce,FIq_Native.field.P,AspisR1SelectedMaskProbe.field.P]

theorem mapped (x : NQ) : map qm (FIq_Native.field.QM31.square x)=
    AspisR1SelectedMaskProbe.field.QM31.square (qm x) := by
  simp only [FIq_Native.field.QM31.square,AspisR1SelectedMaskProbe.field.QM31.square,
    qm,←cm_square,←cm_double,←FIv_NativeCM.mul,←FIv_NativeCM.add,←FIv_NativeCM.by_r,
    bind_map,map_bind,map_ok]
#print axioms cm_double
#print axioms cm_square
#print axioms mapped
end AspisR1.FIx_SquareMap
end
