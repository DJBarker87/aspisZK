import R1Z.PV_RunJoin_QueryLeafWordBounds64
import R1Z.PV_RunJoin_QuerySliceRead64
import R1Z.PV_RunJoin_QueryFillStep64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_QueryStoredWords64
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]

theorem enough (words : alloc.vec.Vec host_commitment.Word) (lanes : alloc.vec.Vec Usize)
    (small : lanes.length≤29)
    (reads : ∀ j : Usize,j.val<lanes.length → ∃ word,
      Slice.index_usize (alloc.vec.Vec.deref words) j=ok word) :
    lanes.length≤words.length := by
  by_cases empty : lanes.length=0
  · omega
  · let j : Usize := UScalar.ofNatCore (lanes.length-1) (by
      have h := PV_RunJoin_SamplerByteIndices54.size
      rw [UScalar.size_def] at h
      omega)
    obtain ⟨word,hr⟩ := reads j (by change lanes.length-1<lanes.length;omega)
    have h := PV_RunJoin_QuerySliceRead64.bound (alloc.vec.Vec.deref words) j word hr
    change lanes.length-1<words.length at h
    omega

theorem complete (c : host_commitment.Commitment)
    (small : c.lanes.length≤29) (lanes : ∀ lane∈c.lanes.val,lane.val<29)
    (out : Array U8 480#usize × Usize)
    (success : host_commitment.commitment_leaf_bytes (alloc.vec.Vec.deref c.words)
      (alloc.vec.Vec.deref c.lanes) 262143#usize=ok out) :
    PV_RunJoin_QueryFillStep64.Domain c := by
  have reads := fun j (h : j.val<c.lanes.length) =>
    PV_RunJoin_QueryLeafWordBounds64.complete (alloc.vec.Vec.deref c.words)
      (alloc.vec.Vec.deref c.lanes) small out success j h
  have enough : c.lanes.length≤c.words.length := enough c.words c.lanes small
    (fun j h => let ⟨word,hr,_⟩ := reads j h; ⟨word,hr⟩)
  refine ⟨small,enough,lanes,?_⟩
  intro j bound
  let index : Usize := UScalar.ofNatCore j (by
    have h := PV_RunJoin_SamplerByteIndices54.size
    rw [UScalar.size_def] at h
    omega)
  obtain ⟨word,hr,size⟩ := reads index bound
  obtain ⟨hw,hvalue⟩ := PV_RunJoin_QuerySliceRead64.value (alloc.vec.Vec.deref c.words) index word hr
  change c.words.val[j]'hw=word at hvalue
  rw [← hvalue] at size
  exact size

#print axioms enough
#print axioms complete
end R1Z.PV_RunJoin_QueryStoredWords64
