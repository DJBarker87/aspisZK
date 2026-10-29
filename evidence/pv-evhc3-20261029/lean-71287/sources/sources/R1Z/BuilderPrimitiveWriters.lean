import R1Z.BuilderBankMerge

/-! Primitive writer identity across the aggregate and original extractions.
Symbolic suffix induction preserves complete Result behaviour. -/
set_option autoImplicit false
namespace R1Z.BuilderPrimitiveWriters
open Aeneas Aeneas.Std Result R0Z.WriterRefine
abbrev S := AspisBuilderGlueSource.aspis_r0_writer_copies.OccRecord
abbrev T := R0WriterCopies.OccRecord
def occRecord (x : S) : T := ⟨x.occupied,x.inverse,x.commitment,x.selected,x.has_selected⟩

theorem m31_sub (a : Std.U32) (b : Std.U32) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.m31_sub a b =
      R0WriterCopies.m31_sub a b := by
  simp only [AspisBuilderGlueSource.aspis_r0_writer_copies.m31_sub, R0WriterCopies.m31_sub, occRecord, AspisBuilderGlueSource.aspis_r0_writer_copies.P, R0WriterCopies.P]

theorem write_value_block_loop0_loop0 (block : Array Std.U32 256#usize) (raw1 : Std.U32) (base : Std.Usize)
  (bit : Std.U32) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.write_value_block_loop0_loop0 block raw1 base bit =
      R0WriterCopies.write_value_block_loop0_loop0 block raw1 base bit := by
  generalize he : 30-bit.val = remaining
  induction remaining using Nat.strong_induction_on generalizing block raw1 base bit with
  | h remaining ih =>
    rw [AspisBuilderGlueSource.aspis_r0_writer_copies.write_value_block_loop0_loop0, R0WriterCopies.write_value_block_loop0_loop0]
    simp only [m31_sub, lift]
    by_cases hit : bit.val < 30
    · have ht : bit < 30#u32 := by simpa [UScalar.lt_equiv] using hit
      simp only [if_pos ht]
      have hn : (U32.wrapping_add bit 1#u32).val = bit.val+1 := by
        rw [U32.wrapping_add_val_eq]; exact Nat.mod_eq_of_lt (by rw [UScalar.size_def]; simp; omega)
      have hnext : ∀ (block : Array Std.U32 256#usize) (raw1 : Std.U32) (base : Std.Usize)
  ,
          AspisBuilderGlueSource.aspis_r0_writer_copies.write_value_block_loop0_loop0 block raw1 base (U32.wrapping_add bit 1#u32) =
            R0WriterCopies.write_value_block_loop0_loop0 block raw1 base (U32.wrapping_add bit 1#u32) := by
        intros block raw1 base
        exact ih (30-(U32.wrapping_add bit 1#u32).val) (by omega)
          block raw1 base (U32.wrapping_add bit 1#u32) rfl
      simp only [bind_tc_ok, hnext]
    · simp only [if_neg (show ¬bit < 30#u32 by simpa [UScalar.lt_equiv] using hit)]

theorem write_value_block_loop0 (values : Array Std.U32 3#usize) (block : Array Std.U32 256#usize)
  (j : Std.Usize) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.write_value_block_loop0 values block j =
      R0WriterCopies.write_value_block_loop0 values block j := by
  generalize he : 3-j.val = remaining
  induction remaining using Nat.strong_induction_on generalizing values block j with
  | h remaining ih =>
    rw [AspisBuilderGlueSource.aspis_r0_writer_copies.write_value_block_loop0, R0WriterCopies.write_value_block_loop0]
    simp only [m31_sub, write_value_block_loop0_loop0, lift]
    by_cases hit : j.val < 3
    · have ht : j < 3#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_pos ht]
      have hn : (Usize.wrapping_add j 1#usize).val = j.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (values : Array Std.U32 3#usize) (block : Array Std.U32 256#usize)
  ,
          AspisBuilderGlueSource.aspis_r0_writer_copies.write_value_block_loop0 values block (Usize.wrapping_add j 1#usize) =
            R0WriterCopies.write_value_block_loop0 values block (Usize.wrapping_add j 1#usize) := by
        intros values block
        exact ih (3-(Usize.wrapping_add j 1#usize).val) (by omega)
          values block (Usize.wrapping_add j 1#usize) rfl
      simp only [bind_tc_ok, hnext]
    · simp only [if_neg (show ¬j < 3#usize by simpa [UScalar.lt_equiv] using hit)]

theorem write_value_block (values : Array Std.U32 3#usize) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.write_value_block values =
      R0WriterCopies.write_value_block values := by
  simp only [AspisBuilderGlueSource.aspis_r0_writer_copies.write_value_block, R0WriterCopies.write_value_block, m31_sub, write_value_block_loop0_loop0, write_value_block_loop0, occRecord, AspisBuilderGlueSource.aspis_r0_writer_copies.P, R0WriterCopies.P]

theorem write_occupancy_row_loop (a : Array Std.U32 8#usize) (block : Array Std.U32 256#usize)
  (base : Std.Usize) (lane : Std.Usize) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.write_occupancy_row_loop a block base lane =
      R0WriterCopies.write_occupancy_row_loop a block base lane := by
  generalize he : 8-lane.val = remaining
  induction remaining using Nat.strong_induction_on generalizing a block base lane with
  | h remaining ih =>
    rw [AspisBuilderGlueSource.aspis_r0_writer_copies.write_occupancy_row_loop, R0WriterCopies.write_occupancy_row_loop]
    simp only [m31_sub, write_value_block_loop0_loop0, write_value_block_loop0, write_value_block, lift]
    by_cases hit : lane.val < 8
    · have ht : lane < 8#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_pos ht]
      have hn : (Usize.wrapping_add lane 1#usize).val = lane.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (a : Array Std.U32 8#usize) (block : Array Std.U32 256#usize)
  (base : Std.Usize) ,
          AspisBuilderGlueSource.aspis_r0_writer_copies.write_occupancy_row_loop a block base (Usize.wrapping_add lane 1#usize) =
            R0WriterCopies.write_occupancy_row_loop a block base (Usize.wrapping_add lane 1#usize) := by
        intros a block base
        exact ih (8-(Usize.wrapping_add lane 1#usize).val) (by omega)
          a block base (Usize.wrapping_add lane 1#usize) rfl
      simp only [bind_tc_ok, hnext]
    · simp only [if_neg (show ¬lane < 8#usize by simpa [UScalar.lt_equiv] using hit)]

theorem write_occupancy_row (block : Array Std.U32 256#usize) (local_row : Std.Usize) (occ : S) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.write_occupancy_row block local_row occ =
      R0WriterCopies.write_occupancy_row block local_row (occRecord occ) := by
  simp only [AspisBuilderGlueSource.aspis_r0_writer_copies.write_occupancy_row, R0WriterCopies.write_occupancy_row, m31_sub, write_value_block_loop0_loop0, write_value_block_loop0, write_value_block, write_occupancy_row_loop, occRecord, AspisBuilderGlueSource.aspis_r0_writer_copies.P, R0WriterCopies.P]

theorem write_aux_block (values : Array Std.U32 3#usize) (input : S) (output : S) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.write_aux_block values input output =
      R0WriterCopies.write_aux_block values (occRecord input) (occRecord output) := by
  simp only [AspisBuilderGlueSource.aspis_r0_writer_copies.write_aux_block, R0WriterCopies.write_aux_block, m31_sub, write_value_block_loop0_loop0, write_value_block_loop0, write_value_block, write_occupancy_row_loop, write_occupancy_row, occRecord, AspisBuilderGlueSource.aspis_r0_writer_copies.P, R0WriterCopies.P]

theorem path_base_local_row (level : Std.Usize) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.path_base_local_row level =
      R0WriterCopies.path_base_local_row level := by
  simp only [AspisBuilderGlueSource.aspis_r0_writer_copies.path_base_local_row, R0WriterCopies.path_base_local_row, m31_sub, write_value_block_loop0_loop0, write_value_block_loop0, write_value_block, write_occupancy_row_loop, write_occupancy_row, write_aux_block, occRecord, AspisBuilderGlueSource.aspis_r0_writer_copies.P, R0WriterCopies.P]

theorem write_path_level_loop (current : Array Std.U32 8#usize) (left : Array Std.U32 8#usize)
  (right : Array Std.U32 8#usize) (buf : Array Std.U32 1536#usize)
  (base : Std.Usize) (lane : Std.Usize) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.write_path_level_loop current left right buf base lane =
      R0WriterCopies.write_path_level_loop current left right buf base lane := by
  generalize he : 8-lane.val = remaining
  induction remaining using Nat.strong_induction_on generalizing current left right buf base lane with
  | h remaining ih =>
    rw [AspisBuilderGlueSource.aspis_r0_writer_copies.write_path_level_loop, R0WriterCopies.write_path_level_loop]
    simp only [m31_sub, write_value_block_loop0_loop0, write_value_block_loop0, write_value_block, write_occupancy_row_loop, write_occupancy_row, write_aux_block, path_base_local_row, lift]
    by_cases hit : lane.val < 8
    · have ht : lane < 8#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_pos ht]
      have hn : (Usize.wrapping_add lane 1#usize).val = lane.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (current : Array Std.U32 8#usize) (left : Array Std.U32 8#usize)
  (right : Array Std.U32 8#usize) (buf : Array Std.U32 1536#usize)
  (base : Std.Usize) ,
          AspisBuilderGlueSource.aspis_r0_writer_copies.write_path_level_loop current left right buf base (Usize.wrapping_add lane 1#usize) =
            R0WriterCopies.write_path_level_loop current left right buf base (Usize.wrapping_add lane 1#usize) := by
        intros current left right buf base
        exact ih (8-(Usize.wrapping_add lane 1#usize).val) (by omega)
          current left right buf base (Usize.wrapping_add lane 1#usize) rfl
      simp only [bind_tc_ok, hnext]
    · simp only [if_neg (show ¬lane < 8#usize by simpa [UScalar.lt_equiv] using hit)]

theorem write_path_level (buf : Array Std.U32 1536#usize) (level : Std.Usize) (bit : Std.U32)
  (current : Array Std.U32 8#usize) (left : Array Std.U32 8#usize)
  (right : Array Std.U32 8#usize) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.write_path_level buf level bit current left right =
      R0WriterCopies.write_path_level buf level bit current left right := by
  simp only [AspisBuilderGlueSource.aspis_r0_writer_copies.write_path_level, R0WriterCopies.write_path_level, m31_sub, write_value_block_loop0_loop0, write_value_block_loop0, write_value_block, write_occupancy_row_loop, write_occupancy_row, write_aux_block, path_base_local_row, write_path_level_loop, occRecord, AspisBuilderGlueSource.aspis_r0_writer_copies.P, R0WriterCopies.P]

theorem write_path_block_loop (bits : Array Std.U32 24#usize)
  (current : Array (Array Std.U32 8#usize) 24#usize)
  (left : Array (Array Std.U32 8#usize) 24#usize)
  (right : Array (Array Std.U32 8#usize) 24#usize)
  (buf : Array Std.U32 1536#usize) (level : Std.Usize) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.write_path_block_loop bits current left right buf level =
      R0WriterCopies.write_path_block_loop bits current left right buf level := by
  generalize he : 24-level.val = remaining
  induction remaining using Nat.strong_induction_on generalizing bits current left right buf level with
  | h remaining ih =>
    rw [AspisBuilderGlueSource.aspis_r0_writer_copies.write_path_block_loop, R0WriterCopies.write_path_block_loop]
    simp only [m31_sub, write_value_block_loop0_loop0, write_value_block_loop0, write_value_block, write_occupancy_row_loop, write_occupancy_row, write_aux_block, path_base_local_row, write_path_level_loop, write_path_level, lift]
    by_cases hit : level.val < 24
    · have ht : level < 24#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_pos ht]
      have hn : (Usize.wrapping_add level 1#usize).val = level.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ (bits : Array Std.U32 24#usize)
  (current : Array (Array Std.U32 8#usize) 24#usize)
  (left : Array (Array Std.U32 8#usize) 24#usize)
  (right : Array (Array Std.U32 8#usize) 24#usize)
  (buf : Array Std.U32 1536#usize) ,
          AspisBuilderGlueSource.aspis_r0_writer_copies.write_path_block_loop bits current left right buf (Usize.wrapping_add level 1#usize) =
            R0WriterCopies.write_path_block_loop bits current left right buf (Usize.wrapping_add level 1#usize) := by
        intros bits current left right buf
        exact ih (24-(Usize.wrapping_add level 1#usize).val) (by omega)
          bits current left right buf (Usize.wrapping_add level 1#usize) rfl
      simp only [bind_tc_ok, hnext]
    · simp only [if_neg (show ¬level < 24#usize by simpa [UScalar.lt_equiv] using hit)]

theorem write_path_block (bits : Array Std.U32 24#usize)
  (current : Array (Array Std.U32 8#usize) 24#usize)
  (left : Array (Array Std.U32 8#usize) 24#usize)
  (right : Array (Array Std.U32 8#usize) 24#usize) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.write_path_block bits current left right =
      R0WriterCopies.write_path_block bits current left right := by
  simp only [AspisBuilderGlueSource.aspis_r0_writer_copies.write_path_block, R0WriterCopies.write_path_block, m31_sub, write_value_block_loop0_loop0, write_value_block_loop0, write_value_block, write_occupancy_row_loop, write_occupancy_row, write_aux_block, path_base_local_row, write_path_level_loop, write_path_level, write_path_block_loop, occRecord, AspisBuilderGlueSource.aspis_r0_writer_copies.P, R0WriterCopies.P]

#print axioms m31_sub
#print axioms write_value_block_loop0_loop0
#print axioms write_value_block_loop0
#print axioms write_value_block
#print axioms write_occupancy_row_loop
#print axioms write_occupancy_row
#print axioms write_aux_block
#print axioms path_base_local_row
#print axioms write_path_level_loop
#print axioms write_path_level
#print axioms write_path_block_loop
#print axioms write_path_block
end R1Z.BuilderPrimitiveWriters
