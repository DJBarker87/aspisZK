import Port4B_VerifyRun

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_SliceReads
open Aeneas Aeneas.Std Result
open MultiproofConeRef MultiproofConeCanonical MultiproofConePhysicalViews

/-- A successful native index-prefix read derives its own bound and content. -/
theorem indices (idx : Array U32 16#usize) (n : Usize) (front : Slice U32)
    (read : core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      idx {«end»:=n}=ok front) : front.val=idx.val.take n.val ∧ n.val≤16 := by
  simp only [Array.index_SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index] at read
  split at read
  next bound =>
    have same := Result.ok.inj read
    refine ⟨(congrArg (fun x : Slice U32 => x.val) same).symm,?_⟩
    simpa using bound
  next bad => cases read

/-- The same physical prefix is exactly P6's live index view. -/
theorem live_indices (s : reference.Scratch) (front : Slice U32)
    (read : core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U32))
      s.idx {«end»:=s.n}=ok front) :
    front.val.map UScalar.val=(live s 0 s.n.val).map Prod.fst := by
  have len : s.idx.val.length=16 := s.idx.property
  obtain ⟨content,bound⟩ := indices s.idx s.n front read
  rw [content]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_take,s.idx.property,MultiproofConeRootGuard.live_length]
    change min s.n.val 16=s.n.val
    exact Nat.min_eq_left bound
  · intro j hj hj'
    have room : j<s.n.val := by
      simpa only [List.length_map,MultiproofConeRootGuard.live_length] using hj'
    simp only [List.getElem_map,List.getElem_take,live,MultiproofConePhysicalLive.view,
      List.getElem_range,Function.comp_apply,decodeEntry,MultiproofConePhysicalLive.cell,Nat.zero_add]
    rw [getElem!_pos s.idx.val j (by omega)]

/-- The accepted count's byte multiplication cannot wrap. -/
theorem scaled (count : Usize) (bound : count.val≤288) :
    (Usize.wrapping_mul 32#usize count).val=32*count.val := by
  rw [Usize.wrapping_mul_val_eq]
  apply Nat.mod_eq_of_lt
  have cap : 9216<UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
  change 32*count.val<UScalar.size .Usize
  omega

#print axioms indices
#print axioms live_indices
#print axioms scaled
end AspisR1.Port4B_SliceReads
end
