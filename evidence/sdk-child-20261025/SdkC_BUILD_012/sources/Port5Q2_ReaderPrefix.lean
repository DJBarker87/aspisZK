import Port5Q2_ReaderRaw
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port5Q2_ReaderPrefix
open Aeneas Aeneas.Std Result

theorem read (q : Array U32 22#usize) (i : Usize) (bound : i.val≤q.val.length) :
    ∃ s : Slice U32,
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice U32)) q {«end»:=i}=ok s ∧
      s.val=q.val.take i.val := by
  simp only [Array.index_SliceIndexRangeToUsizeSlice,core.slice.index.SliceIndexRangeToUsizeSlice.index]
  have h : i.val≤q.to_slice.length := bound
  rw [if_pos h]
  exact ⟨_,rfl,by simp only [List.slice,Array.to_slice,List.extract_eq_drop_take,Nat.sub_zero,List.drop_zero]⟩

#print axioms read
end AspisR1.Port5Q2_ReaderPrefix
end
