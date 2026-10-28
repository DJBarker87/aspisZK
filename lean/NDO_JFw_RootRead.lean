import RPz7_PSem_Root
set_option autoImplicit false
namespace AspisR1.JFw_RootRead
open Aeneas Aeneas.Std Result

theorem read (bytes : Slice U8) (bound : 32 ≤ bytes.length) :
    ∃ (s : Slice U8) (root : Array U8 32#usize),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
        bytes {«end»:=32#usize} = ok s ∧
      core.array.TryFromSharedArraySlice.try_from 32#usize s = ok (.Ok root) := by
  change 32 ≤ bytes.val.length at bound
  let s : Slice U8 := ⟨bytes.val.take 32,by
    have h := bytes.property
    simp only [List.length_take]
    omega⟩
  have length : s.val.length = 32 := by
    change (bytes.val.take 32).length = 32
    rw [List.length_take]
    omega
  let root : Array U8 32#usize := ⟨s.val,length⟩
  refine ⟨s,root,?_,?_⟩
  · simp only [Slice.index_SliceIndexRangeToUsizeSliceInst]
    unfold core.slice.index.SliceIndexRangeToUsizeSlice.index
    have fits : (32#usize).val ≤ bytes.length := bound
    rw [if_pos fits]
    apply congrArg Result.ok
    apply Subtype.ext
    simp only [List.slice,List.drop_zero,s,show (32#usize).val = 32 from rfl,Nat.sub_zero]
  · have size : Slice.len s = 32#usize := by
      apply UScalar.eq_of_val_eq
      exact length
    unfold core.array.TryFromSharedArraySlice.try_from
    rw [dif_pos size]

#print axioms read
end AspisR1.JFw_RootRead
