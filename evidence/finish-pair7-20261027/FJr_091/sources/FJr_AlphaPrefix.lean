import FJc_SliceCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJr_AlphaPrefix
open Aeneas Aeneas.Std Result
open AspisR1Stage2.Stage2Finish

theorem value {N : Usize} (point : Array E N) (selected : Slice E) (bound : 2≤N.val)
    (run : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) point ⟨2#usize⟩=ok selected) :
    selected.val=point.val.take 2 ∧ Slice.len (FIo_Install.toSlice selected)=2#usize := by
  unfold core.array.Array.index core.ops.index.IndexSlice core.slice.index.Slice.index
    core.slice.index.SliceIndexRangeToUsizeSlice core.slice.index.SliceIndexRangeToUsizeSlice.index at run
  simp only [Array.to_slice] at run
  split at run
  · cases Result.ok.inj run
    refine ⟨rfl,?_⟩
    apply UScalar.eq_of_val_eq
    rw [Slice.len_val]
    change ((point.val.take 2).map FIo_Install.toE).length=2
    rw [List.length_map,List.length_take,point.property,Nat.min_eq_left bound]
  · cases run

theorem canonical {N : Usize} (point : Array E N) (selected : Slice E) (bound : 2≤N.val)
    (cp : ∀ x∈point.val,FIo_WideValues.Canon (FIo_Install.toE x))
    (run : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice E)) point ⟨2#usize⟩=ok selected) :
    ∀ x∈(FIo_Install.toSlice selected).val,FIo_WideValues.Canon x := by
  have vals := (value point selected bound run).1
  intro x hx
  change x∈selected.val.map FIo_Install.toE at hx
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
  rw [vals] at hy
  exact cp y (List.mem_of_mem_take hy)

#print axioms value
#print axioms canonical
end AspisR1.FJr_AlphaPrefix
end
