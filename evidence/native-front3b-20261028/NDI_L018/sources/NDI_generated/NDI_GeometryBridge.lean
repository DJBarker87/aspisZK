import NDI_GeometryRef.Funs
import S7OwnedP6QueryRead
set_option autoImplicit false
namespace NDI_GeometryBridge
open Aeneas Aeneas.Std Result

def rows (g : S7OwnedP6QueryRead.QueryGeometry) : Slice (Array U32 5#usize) :=
  ⟨g.inverses.val,g.inverses.property⟩

theorem reference (g : S7OwnedP6QueryRead.QueryGeometry) (index : Usize) :
    NDI_GeometryRef.geometry_ref (rows g) g.start index =
      S7OwnedP6QueryRead.QueryGeometry.for_query g index := by
  unfold NDI_GeometryRef.geometry_ref S7OwnedP6QueryRead.QueryGeometry.for_query
  rfl

theorem caller (g : S7OwnedP6QueryRead.QueryGeometry) (index stop : Usize)
    (lo : g.start.val≤index.val) (hi : index.val<stop.val)
    (length : g.inverses.val.length=stop.val-g.start.val) (cap : stop.val≤22) :
    g.start.val≤index.val ∧ index.val-g.start.val<g.inverses.val.length ∧
      g.inverses.val.length≤22 := by omega

#print axioms reference
#print axioms caller
end NDI_GeometryBridge
