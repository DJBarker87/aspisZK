import NFP_QueryCuts
import Port5Q1_GeometryAccessor
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_GeometryDomains
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts
/-- Accessor domains come from the SAME geometry record and reached index.
Canonicality/start/length are root input predicates; no new producer success. -/
theorem reads (geometry : verifier.QueryGeometry) (i finish : Usize)
 (lo : geometry.start.val ≤ i.val) (hi : i.val < finish.val)
 (isize : geometry.inverses.val.length=finish.val-geometry.start.val)
 (zsize : geometry.line_z.val.length=finish.val-geometry.start.val)
 (ic : ∀ a∈geometry.inverses.val, ∀ x∈a.val,x.val<2147483647)
 (zc : ∀ x∈geometry.line_z.val,x.val<2147483647) :
 ∃ inverse z, Port5Q1_GeometryBinding.forQuery geometry i=ok inverse ∧
 alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
  geometry.line_z (Usize.wrapping_sub i geometry.start)=ok z ∧
 (∀ x∈inverse.val,x.val<2147483647) ∧ z.val<2147483647 := by
 have offset := Port5Q1_GeometryAccessor.offset i geometry.start lo
 have ib : (Usize.wrapping_sub i geometry.start).val<geometry.inverses.val.length := by
  rw [offset,isize];omega
 have zb : (Usize.wrapping_sub i geometry.start).val<geometry.line_z.val.length := by
  rw [offset,zsize];omega
 obtain ⟨inverse,readi,pointi⟩ := WP.spec_imp_exists
  (alloc.vec.Vec.index_usize_spec geometry.inverses (Usize.wrapping_sub i geometry.start) ib)
 obtain ⟨z,readz,pointz⟩ := WP.spec_imp_exists
  (alloc.vec.Vec.index_usize_spec geometry.line_z (Usize.wrapping_sub i geometry.start) zb)
 refine ⟨inverse,z,readi,readz,?_,?_⟩
 · apply ic inverse
   rw [pointi]
   exact List.getElem_mem _
 · apply zc z
   rw [pointz]
   exact List.getElem_mem _
#print axioms reads
end AspisR1.NFP_GeometryDomains
end
