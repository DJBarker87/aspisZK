import R1Z.BuilderBankShape
import R1Z.BuilderRecordsPath

/-! The actual extracted bank dispatcher reads the Parts table cellwise.
No assumption about the origin or cryptographic meaning of Parts is made. -/
set_option autoImplicit false
namespace R1Z.BuilderBankCells
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder

def cell (pt : Parts) (c r : Nat) : U32 :=
  if c < 16 then
    if r < 912 then (pt.blocks.val[r/16]!).val[(r%16)*16+c]!
    else if r < 1008 then pt.path.val[(r-912)*16+c]!
    else pt.aux.val[(r-1008)*16+c]!
  else 0#u32

theorem vec_index {α : Type} [Inhabited α] (v : alloc.vec.Vec α) (i : Usize)
    (hi : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice α) v i = ok v.val[i.val]! := by
  rw [alloc.vec.Vec.index_slice_index]
  unfold alloc.vec.Vec.index_usize
  change (match v.val[i.val]? with | none => fail .arrayOutOfBounds | some x => ok x) = _
  rw [List.getElem?_eq_getElem hi]
  simp only [getElem!_pos v.val i.val hi]

theorem copy_cell (pt : Parts) (hblocks : pt.blocks.val.length = 57)
    (c r : Usize) (hr : r.val < 1024) :
    AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.copy_cell pt c r =
      ok (cell pt c.val r.val) := by
  rw [AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.copy_cell]
  simp only [C1_COLS, PATH_ROW0, AUX_ROW0]
  unfold cell
  by_cases hc : c.val < 16
  · rw [if_pos (by simpa [UScalar.lt_equiv] using hc), if_pos hc]
    by_cases hpath : r.val < 912
    · rw [if_pos (by simpa [UScalar.lt_equiv] using hpath), if_pos hpath]
      obtain ⟨q,hq,vq⟩ := UScalar.div_spec r (y := 16#usize) (by simp)
      rw [hq]
      simp only [bind_tc_ok]
      rw [vec_index _ q (by simp only [hblocks, vq]; simp; omega)]
      simp only [bind_tc_ok]
      obtain ⟨rem,hrem,vrem⟩ := WP.spec_imp_exists (UScalar.rem_spec r (y := 16#usize) (by simp))
      rw [hrem]
      simp only [bind_tc_ok, lift]
      have vq' : q.val = r.val/16 := by simpa using vq
      have vr : rem.val = r.val%16 := by simpa using vrem
      have vm : (Usize.wrapping_mul rem 16#usize).val = (r.val%16)*16 := by
        rw [umul _ _ (by simp; omega)]; simp only [vr, UScalar.ofNatCore_val_eq]
      have va : (Usize.wrapping_add (Usize.wrapping_mul rem 16#usize) c).val =
          (r.val%16)*16+c.val := by
        rw [uadd _ _ (by rw [vm]; omega), vm]
      rw [index_ok _ _ (by rw [va]; simp; omega)]
      simp only [vq',va]
    · rw [if_neg (by simpa [UScalar.lt_equiv] using hpath), if_neg hpath]
      by_cases haux : r.val < 1008
      · rw [if_pos (by simpa [UScalar.lt_equiv] using haux), if_pos haux]
        simp only [lift,bind_tc_ok]
        have vs : (Usize.wrapping_sub r 912#usize).val = r.val-912 := by
          simpa using BuilderRecordsPath.sub_val r 912#usize (by simp; omega)
        have vm : (Usize.wrapping_mul (Usize.wrapping_sub r 912#usize) 16#usize).val =
            (r.val-912)*16 := by
          rw [umul _ _ (by rw [vs]; simp; omega), vs]; rfl
        have va : (Usize.wrapping_add
            (Usize.wrapping_mul (Usize.wrapping_sub r 912#usize) 16#usize) c).val =
            (r.val-912)*16+c.val := by
          rw [uadd _ _ (by rw [vm]; omega),vm]
        rw [index_ok _ _ (by rw [va]; simp; omega)]
        simp only [va]
      · rw [if_neg (by simpa [UScalar.lt_equiv] using haux), if_neg haux]
        simp only [lift,bind_tc_ok]
        have vs : (Usize.wrapping_sub r 1008#usize).val = r.val-1008 := by
          simpa using BuilderRecordsPath.sub_val r 1008#usize (by simp; omega)
        have vm : (Usize.wrapping_mul (Usize.wrapping_sub r 1008#usize) 16#usize).val =
            (r.val-1008)*16 := by
          rw [umul _ _ (by rw [vs]; simp; omega),vs]; rfl
        have va : (Usize.wrapping_add
            (Usize.wrapping_mul (Usize.wrapping_sub r 1008#usize) 16#usize) c).val =
            (r.val-1008)*16+c.val := by
          rw [uadd _ _ (by rw [vm]; omega),vm]
        rw [index_ok _ _ (by rw [va]; simp; omega)]
        simp only [va]
  · rw [if_neg (by simpa [UScalar.lt_equiv] using hc), if_neg hc]

#print axioms vec_index
#print axioms copy_cell
end R1Z.BuilderBankCells
