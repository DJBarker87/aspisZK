import FJh_GroupSlices
import FIw_PackSource
import FJe_ExternalAdjoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJh_SlicePackValue
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State QM Decode Canonical)
open FJh_GroupSlices (sliceAt inputAt)
open FIw_ArrayValue (canonical decoded)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
def pack (a : State) (g : Fin 4) := R0P.poseidonPackingFormula iBasis uBasis
  (fun j=>decoded a (FJe_ExternalAdjoint.lane g j))
/-- The actual width-four native slice and pack, retaining each original lane. -/
theorem value (a : State) (start stop g : Usize) (s : Slice QM) (out : QM)
    (hg : g.val<4) (hs : start.val=4*g.val) (he : stop.val=start.val+4)
    (hb : stop.val≤16) (ca : canonical a)
    (rs : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice QM)) a ⟨start,stop⟩=ok s)
    (rp : field.qm31_pack_base4 s=ok out) :
    Canonical out ∧ Decode out=pack a ⟨g.val,hg⟩ := by
  have hle : start.val≤stop.val := by omega
  have src : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeUsizeSlice QM)) a ⟨start,stop⟩=ok (sliceAt a start stop) := by
    rw [Array.index_SliceIndexRangeUsizeSlice]
    simp only [core.slice.index.SliceIndexRangeUsizeSlice.index]
    have hlen : stop.val≤a.val.length := by
      have ha : a.val.length=16 := by simpa using a.property
      rw [ha];exact hb
    simp [Array.to_slice,Slice.length,hle,hlen,sliceAt]
    exact hb
  have eq : s=sliceAt a start stop := Result.ok.inj (rs.symm.trans src)
  subst s
  have len : (sliceAt a start stop).length=4 :=
    FJh_GroupSlices.slice_length_four a start stop hle hb he
  have can : ∀x∈(sliceAt a start stop).val,Canonical x := by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
    have h4 : j<4 := by simpa only [←len] using hj
    rw [FJh_GroupSlices.slice_input_eq a start stop hle hb he ⟨j,h4⟩]
    exact ca _ (List.getElem_mem _)
  obtain ⟨copied,same,co,vo⟩ := FIw_PackSource.value _ out len can rp
  have cells : (fun j=>FIv_NativeArithmetic.qm (FIw_ArrayValue.cells copied j))=
      (fun j=>FIv_NativeArithmetic.qm (inputAt a start stop he hb j)) := by
    funext j
    unfold FIw_ArrayValue.cells
    simp only [same]
    rw [FJh_GroupSlices.slice_input_eq a start stop hle hb he j]
  refine ⟨co,?_⟩
  rw [vo,cells]
  have decodedCells (j : Fin 4) : Decode (inputAt a start stop he hb j)=
      decoded a (FJe_ExternalAdjoint.lane ⟨g.val,hg⟩ j) := by
    unfold inputAt decoded FIw_ArrayValue.cells FJe_ExternalAdjoint.lane
    simp only [hs]
  simp only [ExtractedMaskQmPackBase4Arithmetic.mathematicalPack,pack,
    R0P.poseidonPackingFormula,decodedCells]
#print axioms value
end AspisR1.FJh_SlicePackValue
end
