import NEO_GetterRef.Funs
import NEO_GeometryGetter
import Port5Q1_GeometryAccessor
set_option autoImplicit false
namespace NEO_GetterReference
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- The independent safe reference and the adopted emitted getter return the
same raw borrowed row on the caller's non-underflow domain. -/
theorem same (g : verifier.QueryGeometry) (i : Usize) (lower : g.start.val≤i.val) :
 NEO_GetterRef.selected g.start i (alloc.vec.Vec.deref g.inverses) =
 NEO_GeometryGetter.read g i := by
 obtain ⟨k,sub,value⟩ := AspisR1.ExtractedCurrentReducerOps.sub_success i g.start lower
 have wrap : Usize.wrapping_sub i g.start=k := by
  apply UScalar.eq_of_val_eq
  exact (Port5Q1_GeometryAccessor.offset i g.start lower).trans value.symm
 simp only [NEO_GetterRef.selected,NEO_GeometryGetter.read,
  S7OwnedP6QueryRead.QueryGeometry.for_query,NEO_GeometryGetter.carrier,sub,wrap,bind_tc_ok,lift]
 rfl

#print axioms same
end NEO_GetterReference
