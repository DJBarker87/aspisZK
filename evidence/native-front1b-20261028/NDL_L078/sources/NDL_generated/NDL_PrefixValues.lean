import NDD_PackPrefix
set_option autoImplicit false
namespace NDL_PrefixValues
open Aeneas Aeneas.Std Result FIq_Native
abbrev Q := field.QM31

theorem zero {R : Type} (k : Q → Q → Q → Q → Result R) :
    NDD_PackPrefix.prefixWith (⟨[],by simp;scalar_tac⟩ : Slice Q) k=k field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO := by
  simp [NDD_PackPrefix.prefixWith,Slice.len,Array.repeat,Array.to_slice,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.from_slice,Array.index_usize,List.setSlice!]

theorem one {R : Type} (a : Q) (k : Q → Q → Q → Q → Result R) :
    NDD_PackPrefix.prefixWith (⟨[a],by simp;scalar_tac⟩ : Slice Q) k=k a field.QM31.ZERO field.QM31.ZERO field.QM31.ZERO := by
  simp [NDD_PackPrefix.prefixWith,Slice.len,Array.repeat,Array.to_slice,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.from_slice,Array.index_usize,List.setSlice!]

theorem two {R : Type} (a b : Q) (k : Q → Q → Q → Q → Result R) :
    NDD_PackPrefix.prefixWith (⟨[a,b],by simp;scalar_tac⟩ : Slice Q) k=k a b field.QM31.ZERO field.QM31.ZERO := by
  simp [NDD_PackPrefix.prefixWith,Slice.len,Array.repeat,Array.to_slice,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.from_slice,Array.index_usize,List.setSlice!]

theorem three {R : Type} (a b c : Q) (k : Q → Q → Q → Q → Result R) :
    NDD_PackPrefix.prefixWith (⟨[a,b,c],by simp;scalar_tac⟩ : Slice Q) k=k a b c field.QM31.ZERO := by
  simp [NDD_PackPrefix.prefixWith,Slice.len,Array.repeat,Array.to_slice,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.from_slice,Array.index_usize,List.setSlice!]

theorem four {R : Type} (a b c d : Q) (k : Q → Q → Q → Q → Result R) :
    NDD_PackPrefix.prefixWith (⟨[a,b,c,d],by simp;scalar_tac⟩ : Slice Q) k=k a b c d := by
  simp [NDD_PackPrefix.prefixWith,Slice.len,Array.repeat,Array.to_slice,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.from_slice,Array.index_usize,List.setSlice!]

#print axioms zero
#print axioms one
#print axioms two
#print axioms three
#print axioms four
end NDL_PrefixValues
