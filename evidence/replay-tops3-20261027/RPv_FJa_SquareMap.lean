import RPu_FIv_Arithmetic
import ExtractedMaskQM31SquareExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_SquareMap
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic
open FIv_Map (map map_bind map_ok)
theorem cm_square (x : NC) : map cm (field.CM31.square x)=
    AspisR1SelectedMaskProbe.field.CM31.square (cm x) := by
  simp only [field.CM31.square,AspisR1SelectedMaskProbe.field.CM31.square,
    cm,map_bind,map_ok,field.P,AspisR1SelectedMaskProbe.field.P,m31_reduce,m31_mul,
    field.M31.double,AspisR1SelectedMaskProbe.field.M31.double,m31_add]
theorem cm_double (x : NC) : map cm (field.CM31.double x)=
    AspisR1SelectedMaskProbe.field.CM31.double (cm x) := by
  simp only [field.CM31.double,AspisR1SelectedMaskProbe.field.CM31.double,
    cm,map_bind,map_ok,field.M31.double,AspisR1SelectedMaskProbe.field.M31.double,m31_add]
  exact FIv_NativeCM.add x x
theorem qm_square (x : NQ) : map qm (field.QM31.square x)=
    AspisR1SelectedMaskProbe.field.QM31.square (qm x) := by
  simp only [field.QM31.square,AspisR1SelectedMaskProbe.field.QM31.square,qm,
    ←cm_square,←FIv_NativeCM.by_r,←FIv_NativeCM.add,←FIv_NativeCM.mul,←cm_double,
    bind_map,map_bind,map_ok]
#print axioms cm_square
#print axioms cm_double
#print axioms qm_square
end AspisR1.FJa_SquareMap
end
