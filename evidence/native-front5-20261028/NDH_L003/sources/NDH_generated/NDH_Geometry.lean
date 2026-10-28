import NDH_Reference.Funs
import AspisR1QueryGeometryActual.Funs
set_option autoImplicit false
namespace NDH_Geometry
open Aeneas Aeneas.Std Result

theorem get (index : AspisR1QueryGeometryActual.domain.FibreIndex) :
    NDH_Reference.fibre_get_ref index = AspisR1QueryGeometryActual.domain.FibreIndex.get index := rfl

theorem table (v : U32 × U32) :
    (do let w ← NDH_Reference.table_ref v
        ok (AspisR1QueryGeometryActual.field.CM31.mk w.1 w.2)) =
      AspisR1QueryGeometryActual.fast_domain.table_value v := by
  cases v
  rfl
#print axioms get
#print axioms table
end NDH_Geometry
