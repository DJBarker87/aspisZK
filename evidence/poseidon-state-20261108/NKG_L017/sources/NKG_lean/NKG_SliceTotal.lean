import RPv_FJh_ProjectedCallValue
import NDO_FIw_PackTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_SliceTotal
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM Canonical)
open FIw_ArrayValue (canonical)
open FJh_GroupSlices (sliceAt)
/-- Exact safe Rust range semantics at this arbitrary four-word window; the
rest of the SAME source array is untouched. -/
theorem slice (a : State) (start finish : Usize)
 (hle : start.val≤finish.val) (hb : finish.val≤16) (span : finish.val=start.val+4)
 (ca : canonical a) :
 FJh_ProjectedCall.slice a start finish=ok (sliceAt a start finish) ∧
 (sliceAt a start finish).length=4 ∧
 (∀ x∈(sliceAt a start finish).val,Canonical x) := by
 have len : (sliceAt a start finish).length=4 :=
   FJh_GroupSlices.slice_length_four a start finish hle hb span
 refine ⟨?_,len,?_⟩
 · rw [FJh_ProjectedCall.slice,Array.index_SliceIndexRangeUsizeSlice]
   simp only [core.slice.index.SliceIndexRangeUsizeSlice.index]
   have hlen : finish.val≤a.val.length := by
     have h : a.val.length=16 := by simpa using a.property
     rw [h];exact hb
   simp [Array.to_slice,Slice.length,hle,hlen,sliceAt]
   exact hb
 · intro x hx
   obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
   have h4 : j<4 := by simpa only [←len] using hj
   rw [FJh_GroupSlices.slice_input_eq a start finish hle hb span ⟨j,h4⟩]
   exact ca _ (List.getElem_mem _)

theorem pack (a : State) (start finish : Usize)
 (hle : start.val≤finish.val) (hb : finish.val≤16) (span : finish.val=start.val+4)
 (ca : canonical a) :
 ∃ out,(do let values ← FJh_ProjectedCall.slice a start finish
           field.qm31_pack_base4 values)=ok out ∧ Canonical out := by
 obtain ⟨rs,len,cs⟩ := slice a start finish hle hb span ca
 obtain ⟨out,rp,cp⟩ := FIw_PackTotal.source (sliceAt a start finish) len cs
 exact ⟨out,by rw [rs,bind_tc_ok,rp],cp⟩
#print slice
#print axioms slice
#print pack
#print axioms pack
end AspisR1.NKG_SliceTotal
end
