import NGO_CheckedOps
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGO_EntryFacts
open AspisR1DecodeKFullV10 NGD_DecodeTrace
/-- Derive every checked arithmetic and original borrowed-window fact from
input bounds. No caller supplies a successful decoder or desired result. -/
theorem construct {N : Usize} {r : Record} {off start : Usize}
    (d : Domain N r off start) :
    ∃ (size finish : Usize) (payload window : Slice U8),
      Usize.checked_mul off 32#usize=some start ∧
      Usize.checked_mul N 32#usize=some size ∧
      Usize.checked_add start size=some finish ∧
      r1_wire.ValidatedRecord.payload r=ok payload ∧
      core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
        payload {start,«end»:=finish}=ok (some window) ∧
      window.val=((r.framed.val.drop 5).drop (32*off.val)).take (32*N.val) := by
  have small : 32*off.val+32*N.val≤3712 := by have h:=d.range;have h1:=d.cap;omega
  let size : Usize := UScalar.ofNat (32*N.val) (by scalar_tac)
  let finish : Usize := UScalar.ofNat (32*off.val+32*N.val) (by scalar_tac)
  have sizeValue : size.val=32*N.val := rfl
  have finishValue : finish.val=32*off.val+32*N.val := rfl
  have offset := NGO_CheckedOps.mul off 32#usize start (by simpa [Nat.mul_comm] using d.start.symm)
  have length := NGO_CheckedOps.mul N 32#usize size (by rw [sizeValue];simp [Nat.mul_comm])
  have addition := NGO_CheckedOps.add start size finish (by rw [d.start,sizeValue,finishValue])
  obtain ⟨payload,original,value⟩ := WP.spec_imp_exists (NGD_DecodeValueTotal.payload_spec r d.minlen)
  have fitting : start≤finish ∧ finish.val≤payload.val.length := by
    constructor
    · change start.val≤finish.val;rw [d.start,finishValue];omega
    · rw [value,finishValue,List.length_drop];exact d.range
  let window : Slice U8 := ⟨List.slice start.val finish.val payload.val,by
    have bound:=payload.property
    simp only [List.slice,List.length_take,List.length_drop]
    omega⟩
  refine ⟨size,finish,payload,window,offset,length,addition,original,?_,?_⟩
  · simp [core.slice.Slice.get,core.slice.index.SliceIndexRangeUsizeSlice,
      core.slice.index.SliceIndexRangeUsizeSlice.get,fitting,window]
  · simp only [window,List.slice,value,d.start,finishValue]
    congr 1
    omega
#print axioms construct
end NGO_EntryFacts
