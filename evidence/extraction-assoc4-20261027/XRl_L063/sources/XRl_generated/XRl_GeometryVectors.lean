import XRk_VectorLength
import Port4C_GeometryStd
open Aeneas Aeneas.Std Result
open XRk_Release
namespace XRl_GeometryVectors
/-- Reuse the coherent cohort's checked scalar-clone/extend theorem. The
release M31 is the same U32 carrier and its clone is definitionally identical. -/
theorem extend (flat out : alloc.vec.Vec aspis_core.field.M31)
    (s : Slice aspis_core.field.M31)
    (run : alloc.vec.Vec.extend_from_slice aspis_core.field.M31.Insts.CoreCloneClone flat s=ok out) :
    out.val=flat.val++s.val := by
  exact AspisR1.Port4C_GeometryStd.extend_fields flat out s run

#print axioms extend
end XRl_GeometryVectors
