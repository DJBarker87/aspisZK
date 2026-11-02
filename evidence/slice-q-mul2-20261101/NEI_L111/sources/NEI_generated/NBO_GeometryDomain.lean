import NBO_QueryRhs
import Port5Q1_GeometryAccessor
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBO_GeometryDomain
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
/-- Derive both checked native geometry offsets and the canonical node input
from the SAME geometry carrier. No selected z or successful read is supplied. -/
theorem node_input (geometry : verifier.QueryGeometry)
 (domain : NBO_QueryDomains.GeometryDomain geometry) (i : Usize) (active : i.val<10) :
 geometry.start.val ≤ i.val ∧
 (Usize.wrapping_sub i geometry.start).val=i.val ∧
 ∃ z, alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32)
   geometry.line_z (Usize.wrapping_sub i geometry.start)=ok z ∧ z.val<2147483647 := by
 have order : geometry.start.val ≤ i.val := by rw [domain.start];change 0 ≤ i.val;omega
 have offset : (Usize.wrapping_sub i geometry.start).val=i.val := by
   rw [Port5Q1_GeometryAccessor.offset i geometry.start order,domain.start]
   rfl
 have bound : (Usize.wrapping_sub i geometry.start).val < geometry.line_z.val.length := by
   rw [offset,domain.lineLength];exact active
 obtain ⟨z,run,contents⟩ := WP.spec_imp_exists
   (alloc.vec.Vec.index_usize_spec geometry.line_z (Usize.wrapping_sub i geometry.start) bound)
 refine ⟨order,offset,z,run,?_⟩
 rw [contents]
 exact domain.line _ (List.getElem_mem _)
#print axioms node_input
end NBO_GeometryDomain
