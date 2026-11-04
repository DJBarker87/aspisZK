import NEW_GeometryPointPrimitives
import NEW_ShiftAssociation
set_option autoImplicit false
namespace NEW_GeometryPoint
open Aeneas Aeneas.Std Result AspisR1
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open NEW_GeometryPointPrimitives

theorem map_point_ok (x y : U32) :
    resultMap toP (ok ({x,y} : P)) = ok ({x,y} : GP) := rfl

/-- Entire point Result for every alias index. Both actual table reads and
both failure/divergence branches are preserved. No child-success premise. -/
theorem complete (u : Usize) :
    resultMap toP (NEW_GeometryActual.fast_domain.fibre_point u) =
      AspisR1QueryGeometryActual.fast_domain.fibre_point NEA_FieldProduct.ops u := by
  simp only [NEW_GeometryActual.fast_domain.fibre_point,
    AspisR1QueryGeometryActual.fast_domain.fibre_point,
    NEW_GeometryActual.aspis_core.r0.domain.FibreIndex.get,
    AspisR1QueryGeometryActual.domain.FibreIndex.get,
    resultMap_bind,map_point_ok,lift,bind_tc_ok,tableA,tableB,
    NEW_ShiftAssociation.checked_to_wrapping]
  generalize ha : Array.index_usize AspisR1QueryGeometryActual.fast_domain.TABLE_A
    (u &&& 511#usize) = a
  cases a with
  | fail e => rfl
  | div => rfl
  | ok a =>
    simp only [bind_tc_ok]
    generalize hb : Array.index_usize AspisR1QueryGeometryActual.fast_domain.TABLE_B
      (Usize.wrapping_shr u 9#u32) = b
    cases b with
    | fail e => rfl
    | div => rfl
    | ok b =>
      rcases a with ⟨a0,a1⟩
      rcases b with ⟨b0,b1⟩
      simp only [NEW_GeometryActual.fast_domain.table_value,
        NEW_GeometryActual.aspis_core.field.CM31.new,
        AspisR1QueryGeometryActual.fast_domain.table_value,NEA_FieldProduct.ops,
        NEA_FieldProduct.toNative,NEA_FieldProduct.ofNative,bind_tc_ok,map_point_ok]
      rw [←NEW_GeometryArithmetic.cm_multiply
        ({a:=a0,b:=a1} : NEW_GeometryPointPrimitives.C)
        ({a:=b0,b:=b1} : NEW_GeometryPointPrimitives.C)]
      cases NEW_GeometryActual.aspis_core.field.CM31.mul
        ({a:=a0,b:=a1} : NEW_GeometryPointPrimitives.C)
        ({a:=b0,b:=b1} : NEW_GeometryPointPrimitives.C) <;> rfl

#print axioms map_point_ok
#print axioms complete
end NEW_GeometryPoint
