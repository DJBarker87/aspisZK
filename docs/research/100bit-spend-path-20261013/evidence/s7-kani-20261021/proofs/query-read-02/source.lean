import Aeneas
import ExtractedCurrentReducerOps
import Lean.Elab.Tactic.Omega
/- Exact emitted geometry layout/read declaration; no external backend. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace S7OwnedP6QueryRead
abbrev aspis_core.field.M31 := U32
structure QueryGeometry where
  start : Std.Usize
  inverses : alloc.vec.Vec (Array aspis_core.field.M31 5#usize)
  line_z : alloc.vec.Vec aspis_core.field.M31

def QueryGeometry.for_query
  (self : QueryGeometry) (index : Std.Usize) :
  Result (Array aspis_core.field.M31 5#usize)
  := do
  let i ← index - self.start
  alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array
    aspis_core.field.M31 5#usize)) self.inverses i


theorem selected_inverse (geometry : QueryGeometry) (index : Usize)
    (hstart : geometry.start.val ≤ index.val)
    (hbound : index.val-geometry.start.val < geometry.inverses.val.length) :
    ∃ selected, QueryGeometry.for_query geometry index = .ok selected ∧
      geometry.inverses.val[index.val-geometry.start.val]? = some selected := by
  obtain ⟨ordinal,hsub,hordinal⟩ :=
    AspisR1.ExtractedCurrentReducerOps.sub_success index geometry.start hstart
  have hb : ordinal.val < geometry.inverses.length := by
    simpa only [hordinal] using hbound
  obtain ⟨selected,hread,hvalue⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_usize_spec geometry.inverses ordinal hb)
  have hs : (index-geometry.start : Result Usize) = .ok ordinal := hsub
  refine ⟨selected,?_,?_⟩
  · simp only [QueryGeometry.for_query,hs,bind_tc_ok]
    exact hread
  · have hget : geometry.inverses.val[ordinal.val]? = some selected := by
      rw [List.getElem?_eq_getElem hb,hvalue]
    simpa only [hordinal] using hget

theorem constructor_range_selects_record (geometry : QueryGeometry) (index finish : Usize)
    (hstart : geometry.start.val ≤ index.val) (hend : index.val<finish.val)
    (hlength : geometry.inverses.val.length=finish.val-geometry.start.val) :
    ∃ selected, QueryGeometry.for_query geometry index = .ok selected ∧
      geometry.inverses.val[index.val-geometry.start.val]? = some selected := by
  apply selected_inverse geometry index hstart
  rw [hlength]
  omega

#print axioms selected_inverse
#print axioms constructor_range_selects_record
end S7OwnedP6QueryRead
