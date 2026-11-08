import NNU_MerkleOpening
set_option autoImplicit false
namespace AspisR1.NNY_OpeningWidth
open Aeneas Aeneas.Std Result
/-- A successful checked opening has width 832 even for an arbitrary wrapped
index. Range ordering itself excludes wraparound of its final addition. -/
theorem source (proof view : Slice U8) (i : Usize)
 (returned : Port4B_Opening.opening proof i=ok view) : view.val.length=832 := by
 let start := Usize.wrapping_add 10055#usize (Usize.wrapping_mul i 832#usize)
 let finish := Usize.wrapping_add start 832#usize
 change core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start:=start,«end»:=finish}=ok view at returned
 obtain ⟨ordered,_,width⟩ := NNU_MerkleOpening.range proof view start finish returned
 have cap : 832 < UScalar.size .Usize := by rw [UScalar.size_def];scalar_tac
 have bounded : start.val < UScalar.size .Usize := by
  rw [UScalar.size_def];exact start.bv.isLt
 have value : finish.val=(start.val+832) % UScalar.size .Usize := by
  change (Usize.wrapping_add start 832#usize).val=_
  rw [Usize.wrapping_add_val_eq]
  rfl
 have noWrap : start.val+832 < UScalar.size .Usize := by
  by_contra overflow
  have reduce : (start.val+832) % UScalar.size .Usize = start.val+832-UScalar.size .Usize :=
   Nat.mod_eq_sub_mod (by omega) |>.trans (Nat.mod_eq_of_lt (by omega))
  omega
 rw [Nat.mod_eq_of_lt noWrap] at value
 omega
#print axioms source
end AspisR1.NNY_OpeningWidth
