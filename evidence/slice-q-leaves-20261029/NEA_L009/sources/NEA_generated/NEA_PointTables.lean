import NEA_PointReference.Funs
import R17FibrePointActualSuccess
set_option autoImplicit false
namespace NEA_PointTables
open Aeneas Aeneas.Std Result

theorem tableA : NEA_PointReference.TABLE_A = AspisR1QueryGeometryActual.fast_domain.TABLE_A := by
  unfold NEA_PointReference.TABLE_A AspisR1QueryGeometryActual.fast_domain.TABLE_A
  rfl

theorem tableB : NEA_PointReference.TABLE_B = AspisR1QueryGeometryActual.fast_domain.TABLE_B := by
  unfold NEA_PointReference.TABLE_B AspisR1QueryGeometryActual.fast_domain.TABLE_B
  rfl
#print axioms tableA
#print axioms tableB
end NEA_PointTables
