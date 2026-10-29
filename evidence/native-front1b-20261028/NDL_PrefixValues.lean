import NDD_PackPrefix
set_option autoImplicit false
namespace NDL_PrefixValues
open Aeneas Aeneas.Std Result FIq_Native
abbrev Q := field.QM31

theorem zero {R : Type} (k : Q → Q → Q → Q → Result R) :
    NDD_PackPrefix.prefixWith (⟨[],by simp <;> scalar_tac⟩ : Slice Q) k=k field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO := by
  simp [NDD_PackPrefix.prefixWith,Slice.len,Array.repeat,Array.to_slice,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.from_slice,Array.index_usize,List.setSlice!]

theorem one {R : Type} (a : Q) (k : Q → Q → Q → Q → Result R) :
    NDD_PackPrefix.prefixWith (⟨[a],by simp <;> scalar_tac⟩ : Slice Q) k=k a field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO := by
  simp [NDD_PackPrefix.prefixWith,Slice.len,Array.repeat,Array.to_slice,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.from_slice,Array.index_usize,List.setSlice!]

theorem two {R : Type} (a b : Q) (k : Q → Q → Q → Q → Result R) :
    NDD_PackPrefix.prefixWith (⟨[a,b],by simp <;> scalar_tac⟩ : Slice Q) k=k a b field.QM31.ZERO field.QM31.ZERO := by
  simp [NDD_PackPrefix.prefixWith,Slice.len,Array.repeat,Array.to_slice,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.from_slice,Array.index_usize,List.setSlice!]

theorem three {R : Type} (a b c : Q) (k : Q → Q → Q → Q → Result R) :
    NDD_PackPrefix.prefixWith (⟨[a,b,c],by simp <;> scalar_tac⟩ : Slice Q) k=k a b c field.QM31.ZERO := by
  simp [NDD_PackPrefix.prefixWith,Slice.len,Array.repeat,Array.to_slice,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.from_slice,Array.index_usize,List.setSlice!]

theorem four {R : Type} (a b c d : Q) (k : Q → Q → Q → Q → Result R) :
    NDD_PackPrefix.prefixWith (⟨[a,b,c,d],by simp <;> scalar_tac⟩ : Slice Q) k=k a b c d := by
  simp [NDD_PackPrefix.prefixWith,Slice.len,Array.repeat,Array.to_slice,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.from_slice,Array.index_usize,List.setSlice!]


def padded (s : Slice Q) (i : Nat) : Q := (s.val[i]?).getD field.QM31.ZERO

theorem all {R : Type} (s : Slice Q) (bound : s.val.length ≤ 4)
    (k : Q → Q → Q → Q → Result R) :
    NDD_PackPrefix.prefixWith s k=k (padded s 0) (padded s 1) (padded s 2) (padded s 3) := by
  rcases s with ⟨xs,hxs⟩
  change xs.length ≤ 4 at bound
  rcases xs with _ | ⟨a,xs⟩
  · simpa [padded] using zero k
  rcases xs with _ | ⟨b,xs⟩
  · simpa [padded] using one a k
  rcases xs with _ | ⟨c,xs⟩
  · simpa [padded] using two a b k
  rcases xs with _ | ⟨d,xs⟩
  · simpa [padded] using three a b c k
  rcases xs with _ | ⟨e,xs⟩
  · simpa [padded] using four a b c d k
  · simp only [List.length_cons] at bound;omega

theorem cohort (s : Slice Q) (bound : s.val.length ≤ 4) :
    (do let q←field.qm31_pack_base4 s;ok (NDD_PackModel.words q))=
      NDD_Reference.pack_ref (Array.make 4#usize
        [NDD_PackModel.words (padded s 0),NDD_PackModel.words (padded s 1),
         NDD_PackModel.words (padded s 2),NDD_PackModel.words (padded s 3)]) := by
  rw [NDD_PackPrefix.source_prefix,all s bound]
  exact (NDD_PackModel.reference_tail _ _ _ _).symm
#print axioms all
#print axioms cohort
#print axioms zero
#print axioms one
#print axioms two
#print axioms three
#print axioms four
end NDL_PrefixValues
