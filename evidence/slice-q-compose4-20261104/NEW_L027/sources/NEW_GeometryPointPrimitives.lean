import NEW_GeometryArithmetic
import NEB_ActualGeometryModel
set_option autoImplicit false
namespace NEW_GeometryPointPrimitives
open Aeneas Aeneas.Std Result AspisR1
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
abbrev C := NEW_GeometryActual.aspis_core.field.CM31
abbrev G := AspisR1QueryGeometryActual.field.CM31
abbrev P := NEW_GeometryActual.aspis_core.r0.domain.Point U32
abbrev GP := AspisR1QueryGeometryActual.domain.Point U32

def toG (x : C) : G := ⟨x.a,x.b⟩
def toP (p : P) : GP := ⟨p.x,p.y⟩

theorem cm_multiply (x y : C) :
    resultMap toG (NEW_GeometryActual.aspis_core.field.CM31.mul x y) =
      NEA_FieldProduct.ops.mul (toG x) (toG y) := by
  change resultMap toG (NEW_GeometryActual.aspis_core.field.CM31.mul x y) =
    (do let z ← FIo_Native.aspis_core.field.CM31.mul
          (NEW_GeometryArithmetic.toC x) (NEW_GeometryArithmetic.toC y)
        ok (NEA_FieldProduct.ofNative z))
  rw [←NEW_GeometryArithmetic.cm_multiply]
  cases NEW_GeometryActual.aspis_core.field.CM31.mul x y <;> rfl

/-- Identical literal frozen tables, not a new field enumeration or exponent proof. -/
theorem tableA : NEW_GeometryActual.fast_domain.TABLE_A =
    AspisR1QueryGeometryActual.fast_domain.TABLE_A := by
  with_unfolding_all rfl

theorem tableB : NEW_GeometryActual.fast_domain.TABLE_B =
    AspisR1QueryGeometryActual.fast_domain.TABLE_B := by
  with_unfolding_all rfl

theorem table_value (p : U32 × U32) :
    resultMap toG (NEW_GeometryActual.fast_domain.table_value p) =
      AspisR1QueryGeometryActual.fast_domain.table_value NEA_FieldProduct.ops p := by
  cases p
  rfl

#print axioms cm_multiply
#print axioms tableA
#print axioms tableB
#print axioms table_value
end NEW_GeometryPointPrimitives
