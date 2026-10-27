import LPr_WordNat
set_option autoImplicit false
namespace AspisR1.LPr_SelectedBytes
open Aeneas Aeneas.Std Result

/-- The actual bounded source index expression, on the SAME expanded carrier. -/
theorem selected (y1 : Slice U8) (len : y1.val.length=928)
    (l : Usize) (live : l.val<29) :
    ∃ b : Slice U8,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) y1
        {start:=Usize.wrapping_mul l 32#usize,
         «end»:=Usize.wrapping_mul (Usize.wrapping_add l 1#usize) 32#usize}=ok b ∧
      b.val.length=32 ∧ b.val=(y1.val.drop (32*l.val)).take 32 := by
  have add : (Usize.wrapping_add l 1#usize).val=l.val+1 := by
    rw [Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt (by scalar_tac)]
    rfl
  have start : (Usize.wrapping_mul l 32#usize).val=32*l.val := by
    rw [Usize.wrapping_mul_val_eq, Nat.mod_eq_of_lt (by scalar_tac)]
    simp only [UScalar.ofNatCore_val_eq]; omega
  have finish : (Usize.wrapping_mul (Usize.wrapping_add l 1#usize) 32#usize).val=32*(l.val+1) := by
    rw [Usize.wrapping_mul_val_eq, add, Nat.mod_eq_of_lt (by scalar_tac)]
    simp only [UScalar.ofNatCore_val_eq]; omega
  let r : core.ops.range.Range Usize :=
    {start:=Usize.wrapping_mul l 32#usize,
     «end»:=Usize.wrapping_mul (Usize.wrapping_add l 1#usize) 32#usize}
  have lo : r.start≤r.end := by simp only [r,UScalar.le_equiv,start,finish]; omega
  have hi : r.end≤y1.length := by simp only [r,UScalar.le_equiv,finish,Slice.length,len]; omega
  obtain ⟨b,run,bytes,size⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec r y1 lo hi)
  refine ⟨b,run,?_,?_⟩
  · simpa only [Slice.length,r,start,finish] using size
  · simpa only [r,start,finish,List.slice,Nat.mul_add,Nat.mul_one,
      Nat.add_sub_cancel_left,Nat.add_sub_cancel] using bytes

#print axioms selected
end AspisR1.LPr_SelectedBytes
