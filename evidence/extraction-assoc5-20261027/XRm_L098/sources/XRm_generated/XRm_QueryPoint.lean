import XRm_QueryIndices
import XRm_PointInterpretation
open Aeneas Aeneas.Std Result ControlFlow
open XRk_Release
namespace XRm_QueryPoint
abbrev F := XRm_FieldValues.M31Exact
/-- The actual query word selects these SAME table words and field-valued
point in one successful emitted body. No separate point-call success is input. -/
theorem reached (start : Usize) (it next : core.slice.iter.Iter U32) (query : U32)
    (lines flat outLines outFlat : alloc.vec.Vec aspis_core.field.M31)
    (hnext : core.slice.iter.IteratorSliceIter.next it=ok (some query,next))
    (run : verifier.QueryGeometry.for_range_loop0.body start it lines flat=ok (.cont (next,outLines,outFlat))) :
    ∃ (point : aspis_core.r0.domain.Point aspis_core.field.M31) high a b,
      (UScalar.cast .Usize query)<262144#usize ∧
      fast_domain.fibre_point (UScalar.cast .Usize query)=ok point ∧
      (UScalar.cast .Usize query) >>> 9#i32=ok high ∧
      Array.index_usize fast_domain.TABLE_A ((UScalar.cast .Usize query) &&& 511#usize)=ok a ∧
      Array.index_usize fast_domain.TABLE_B high=ok b ∧
      (point.x.val:F)=(a.1.val:F)*(b.1.val:F)-(a.2.val:F)*(b.2.val:F) ∧
      (point.y.val:F)=(a.1.val:F)*(b.2.val:F)+(a.2.val:F)*(b.1.val:F) := by
  obtain ⟨point,_,_,_,_,_,bound,hpoint,_,_,_,_,_⟩ :=
    XRm_QueryIndices.reached start it next query lines flat outLines outFlat hnext run
  obtain ⟨high,a,b,hh,ha,hb,hx,hy,_,_⟩ :=
    XRm_PointInterpretation.point (UScalar.cast .Usize query) point hpoint
  exact ⟨point,high,a,b,bound,hpoint,hh,ha,hb,hx,hy⟩
#print axioms reached
end XRm_QueryPoint
