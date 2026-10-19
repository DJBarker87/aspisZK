import Aeneas
import AspisR1QueryGeometryActual.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace R17FibrePointSuccessOutput
open AspisR1QueryGeometryActual

/-- Successful-output inversion for the exact Aeneas `fibre_point` body,
with CM31 arithmetic kept as explicit operations rather than external axioms.
All array lookups and scalar-result steps are the actual generated operations. -/
theorem fibre_point_success_output
    (ops : CM31Ops) (u : domain.FibreIndex)
    (ix iA iB : Std.Usize)
    (entryA entryB : Std.U32 × Std.U32)
    (left right product : field.CM31)
    (hget : domain.FibreIndex.get u = ok ix)
    (hmask : lift (ix &&& 511#usize) = ok iA)
    (hlookupA : Array.index_usize fast_domain.TABLE_A iA = ok entryA)
    (hleft : fast_domain.table_value ops entryA = ok left)
    (hshift : ix >>> 9#i32 = ok iB)
    (hlookupB : Array.index_usize fast_domain.TABLE_B iB = ok entryB)
    (hright : fast_domain.table_value ops entryB = ok right)
    (hmul : ops.mul left right = ok product) :
    fast_domain.fibre_point ops u = ok
      ({ x := product.a, y := product.b } : domain.Point field.M31) := by
  simp [fast_domain.fibre_point, hget, hmask, hlookupA, hleft,
    hshift, hlookupB, hright, hmul]

#print axioms fibre_point_success_output
end R17FibrePointSuccessOutput
