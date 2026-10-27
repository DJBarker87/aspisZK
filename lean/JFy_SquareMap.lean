import JFy_FieldTotal
import ExtractedMaskQM31SquareExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SquareMap
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic
open FIv_Map (map map_bind map_ok)

theorem cm_square (x : NC) : map cm (FIq_Native.field.CM31.square x)=
    AspisR1SelectedMaskProbe.field.CM31.square (cm x) := by
  simp only [FIq_Native.field.CM31.square,AspisR1SelectedMaskProbe.field.CM31.square,
    cm,map_bind,map_ok,FIv_NativeArithmetic.m31_reduce,FIv_NativeArithmetic.m31_mul,
    FIq_Native.field.M31.double,AspisR1SelectedMaskProbe.field.M31.double,
    FIv_NativeArithmetic.m31_add,FIq_Native.field.P,AspisR1SelectedMaskProbe.field.P]
#print axioms cm_square

theorem cm_double (x : NC) : map cm (FIq_Native.field.CM31.double x)=
    AspisR1SelectedMaskProbe.field.CM31.double (cm x) := FIv_NativeCM.add x x
#print axioms cm_double

theorem source (x : NQ) : map qm (FIq_Native.field.QM31.square x)=
    AspisR1SelectedMaskProbe.field.QM31.square (qm x) := by
  simp only [FIq_Native.field.QM31.square,AspisR1SelectedMaskProbe.field.QM31.square,qm,
    ← cm_square,← cm_double,← FIv_NativeCM.add,← FIv_NativeCM.mul,← FIv_NativeCM.by_r,
    bind_map,map_bind,map_ok]
#print axioms source
end AspisR1.JFy_SquareMap
end
