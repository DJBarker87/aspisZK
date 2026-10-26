import S1PrepareBufferRecombineV1
set_option autoImplicit false
namespace AspisS1PrepareBufferRecombine
open Aeneas Aeneas.Std Result

/-- The actual deref/split/back/reindex sequence returns exactly the second
replacement slice when both actual replacements preserve their own lengths.
The split back-function's length guard is proved, not silently discarded. -/
theorem y1_recombined (logical : alloc.vec.Vec U8)
    (deref : Slice U8 × (Slice U8 → alloc.vec.Vec U8))
    (parts : (Slice U8 × Slice U8) × ((Slice U8 × Slice U8) → Slice U8))
    (cut : Usize) (semantic y1 returned : Slice U8)
    (hderef : lift (alloc.vec.Vec.deref_mut logical)=ok deref)
    (hsplit : core.slice.Slice.split_at_mut deref.1 cut=ok parts)
    (hsemanticLength : semantic.length=parts.1.1.length)
    (hy1Length : y1.length=parts.1.2.length)
    (hindex : alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
      (deref.2 (parts.2 (semantic,y1))) {start:=cut}=ok returned) : returned=y1 := by
  have derefEq : alloc.vec.Vec.deref_mut logical=deref := Result.ok.inj hderef
  have bound : cut≤deref.1.length := by
    unfold core.slice.Slice.split_at_mut at hsplit
    split at hsplit
    · assumption
    · cases hsplit
  obtain ⟨pair,call,facts⟩ := WP.spec_imp_exists
    (core.slice.Slice.split_at_mut.spec deref.1 cut bound)
  have same : pair=parts := Result.ok.inj (call.symm.trans hsplit)
  subst pair
  have firstLength : semantic.length=cut.val := hsemanticLength.trans facts.1
  have secondLength : y1.length=deref.1.length-cut.val := hy1Length.trans facts.2.1
  have replaced := facts.2.2.2.2 semantic y1 firstLength secondLength
  have vectorBytes : (deref.2 (parts.2 (semantic,y1))).val=semantic.val++y1.val := by
    have backCopy := congrArg (fun p : Slice U8 × (Slice U8 → alloc.vec.Vec U8) =>
      (p.2 (parts.2 (semantic,y1))).val) derefEq
    change (parts.2 (semantic,y1)).val=(deref.2 (parts.2 (semantic,y1))).val at backCopy
    exact backCopy.symm.trans replaced.1
  have vectorBound : cut≤(deref.2 (parts.2 (semantic,y1))).length := by
    change cut.val≤(deref.2 (parts.2 (semantic,y1))).val.length
    rw [vectorBytes,List.length_append]
    change semantic.val.length=cut.val at firstLength
    omega
  obtain ⟨slice,read,readFacts⟩ := WP.spec_imp_exists
    (alloc.vec.Vec.index_RangeFrom_spec (deref.2 (parts.2 (semantic,y1))) {start:=cut} vectorBound)
  have sameSlice : slice=returned := Result.ok.inj (read.symm.trans hindex)
  subst slice
  apply Subtype.ext
  have bytes := readFacts.1
  rw [vectorBytes] at bytes
  change returned.val=y1.val
  rw [bytes]
  have firstBytes : semantic.val.length=cut.val := firstLength
  rw [←firstBytes]
  exact List.drop_left

#print axioms y1_recombined
end AspisS1PrepareBufferRecombine
