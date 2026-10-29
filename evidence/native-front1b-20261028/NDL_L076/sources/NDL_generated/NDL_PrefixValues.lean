import NDD_PackPrefix
set_option autoImplicit false
namespace NDL_PrefixValues
open Aeneas Aeneas.Std Result FIq_Native
abbrev Q := field.QM31

theorem four {R : Type} (a b c d : Q) (k : Q → Q → Q → Q → Result R) :
    NDD_PackPrefix.prefixWith (⟨[a,b,c,d],by simp;scalar_tac⟩ : Slice Q) k=k a b c d := by
  simp [NDD_PackPrefix.prefixWith,Slice.len,Array.repeat,Array.to_slice,
    core.array.Array.index_mut,core.ops.index.IndexMutSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice,Array.from_slice,Array.index_usize]
#print axioms four
end NDL_PrefixValues
