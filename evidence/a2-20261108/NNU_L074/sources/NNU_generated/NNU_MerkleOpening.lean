import NNU_MerkleChildren
set_option autoImplicit false
namespace AspisR1.NNU_MerkleOpening
open Aeneas Aeneas.Std Result MultiproofConeSlices

theorem range (proof view : Slice U8) (start finish : Usize)
 (returned : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=start,«end»:=finish}=.ok view) :
 start.val≤finish.val ∧ finish.val≤proof.val.length ∧ view.val.length=finish.val-start.val := by
 by_cases valid : start≤finish ∧ finish.val≤proof.val.length
 · have same : sub proof start finish=view := Result.ok.inj
     ((range_total proof start finish valid.1 valid.2).symm.trans returned)
   rw [←same]
   exact ⟨valid.1,valid.2,sub_length proof start finish valid.1 valid.2⟩
 · simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeUsizeSlice.index,
     valid,if_false] at returned
   cases returned

theorem source (proof view : Slice U8) (i : Usize) (bound : i.val < 22)
 (returned : Port4B_Opening.opening proof i=.ok view) : view.val.length=832 := by
 let offset := Usize.wrapping_mul i 832#usize
 let start := Usize.wrapping_add 10055#usize offset
 let finish := Usize.wrapping_add start 832#usize
 have cap : 30000 < UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 have ov : offset.val=i.val*832 := by
   change (Usize.wrapping_mul i 832#usize).val=i.val*832
   rw [Usize.wrapping_mul_val_eq]
   apply Nat.mod_eq_of_lt
   change i.val*832 < UScalar.size .Usize
   omega
 have sv : start.val=10055+i.val*832 := by
   change (Usize.wrapping_add 10055#usize offset).val=_
   rw [Usize.wrapping_add_val_eq]
   apply (Nat.mod_eq_of_lt (show (10055#usize).val+offset.val < UScalar.size .Usize by
     rw [ov];change 10055+i.val*832 < _;omega)).trans
   rw [ov];rfl
 have fv : finish.val=start.val+832 := by
   change (Usize.wrapping_add start 832#usize).val=_
   rw [Usize.wrapping_add_val_eq]
   apply Nat.mod_eq_of_lt
   change start.val+832 < UScalar.size .Usize
   omega
 change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   proof {start:=start,«end»:=finish}=.ok view at returned
 have width := (range proof view start finish returned).2.2
 omega
#print axioms range
#print axioms source
end AspisR1.NNU_MerkleOpening
