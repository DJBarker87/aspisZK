import NDH_Reference.Funs
import AspisR1QueryGeometryActual.Funs
set_option autoImplicit false
namespace NDH_Geometry
open Aeneas Aeneas.Std Result

theorem get (index : AspisR1QueryGeometryActual.domain.FibreIndex) :
    NDH_Reference.fibre_get_ref index = AspisR1QueryGeometryActual.domain.FibreIndex.get index := rfl

theorem table (ops : AspisR1QueryGeometryActual.CM31Ops)
    (constructor : ∀ a b, ops.new a b = ok ⟨a,b⟩) (v : U32 × U32) :
    (do let w ← NDH_Reference.table_ref v
        ok (AspisR1QueryGeometryActual.field.CM31.mk w.1 w.2)) =
      AspisR1QueryGeometryActual.fast_domain.table_value ops v := by
  cases v with
  | mk a b => exact (constructor a b).symm
#print axioms get
#print axioms table
end NDH_Geometry
