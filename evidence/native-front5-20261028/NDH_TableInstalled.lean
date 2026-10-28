import NDH_Geometry
import R17CurrentCM31Semantics
set_option autoImplicit false
namespace NDH_TableInstalled
open Aeneas Aeneas.Std Result

theorem reference (v : U32 × U32) :
    (do let w ← NDH_Reference.table_ref v
        ok (AspisR1QueryGeometryActual.field.CM31.mk w.1 w.2)) =
      AspisR1QueryGeometryActual.fast_domain.table_value
        R17CurrentCM31Semantics.operations v :=
  NDH_Geometry.table R17CurrentCM31Semantics.operations (fun _ _ => rfl) v

#print axioms reference
end NDH_TableInstalled
