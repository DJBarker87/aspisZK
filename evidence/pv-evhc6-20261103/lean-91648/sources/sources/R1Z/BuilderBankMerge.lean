import R1Z.BuilderBankExtracted
import R0Z.BuilderWitnessMerged

/-! Symbolic identification of the actual extracted merge callees with the
existing checked writers. No bank cell is enumerated or concretely reduced. -/
set_option autoImplicit false
namespace R1Z.BuilderBankMerge
open Aeneas Aeneas.Std Result R0Z.WriterRefine
abbrev Bank := Array U32 16384#usize

theorem model_count : R0WriterCopies.TRACE_CELLS = ok 16384#usize := by
  obtain ⟨t,ht,hv⟩ := trace_cells
  have he : t = 16384#usize := UScalar.eq_of_val_eq (by simpa using hv)
  simpa only [he] using ht

theorem source_count : AspisBuilderGlueSource.aspis_r0_writer_copies.TRACE_CELLS =
    ok 16384#usize := by
  rw [AspisBuilderGlueSource.aspis_r0_writer_copies.TRACE_CELLS, ← R0WriterCopies.TRACE_CELLS]
  exact model_count

theorem copy_loop (stable late out : Bank) (i : Usize) (hi : i.val ≤ 16384) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.merge_copy_loop stable late out i =
      R0WriterCopies.merge_copy_loop stable late out i := by
  generalize he : 16384-i.val = remaining
  induction remaining using Nat.strong_induction_on generalizing i out with
  | h remaining ih =>
    rw [AspisBuilderGlueSource.aspis_r0_writer_copies.merge_copy_loop,
      R0WriterCopies.merge_copy_loop]
    simp only [source_count, model_count, bind_tc_ok, lift]
    by_cases hit : i.val < 16384
    · have ht : i < 16384#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_pos ht]
      have hn : (Usize.wrapping_add i 1#usize).val = i.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ out : Bank,
          AspisBuilderGlueSource.aspis_r0_writer_copies.merge_copy_loop stable late out
            (Usize.wrapping_add i 1#usize) =
          R0WriterCopies.merge_copy_loop stable late out (Usize.wrapping_add i 1#usize) := by
        intro out
        exact ih (16384-(Usize.wrapping_add i 1#usize).val) (by omega)
          out (Usize.wrapping_add i 1#usize) (by omega) rfl
      simp only [hnext]
    · simp only [if_neg (show ¬i < 16384#usize by simpa [UScalar.lt_equiv] using hit)]

theorem copy (stable late : Bank) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.merge_copy stable late =
      R0WriterCopies.merge_copy stable late := by
  exact copy_loop stable late (Array.repeat 16384#usize 0#u32) 0#usize (by simp)

theorem check_loop (stable late : Bank) (flag : Bool) (i : Usize) (hi : i.val ≤ 16384) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.merge_check_loop stable late flag i =
      R0WriterCopies.merge_check_loop stable late flag i := by
  generalize he : 16384-i.val = remaining
  induction remaining using Nat.strong_induction_on generalizing i flag with
  | h remaining ih =>
    rw [AspisBuilderGlueSource.aspis_r0_writer_copies.merge_check_loop,
      R0WriterCopies.merge_check_loop]
    simp only [source_count, model_count, bind_tc_ok, lift]
    by_cases hit : i.val < 16384
    · have ht : i < 16384#usize := by simpa [UScalar.lt_equiv] using hit
      simp only [if_pos ht]
      have hn : (Usize.wrapping_add i 1#usize).val = i.val+1 := by
        rw [uadd _ _ (by simp; omega)]; rfl
      have hnext : ∀ flag : Bool,
          AspisBuilderGlueSource.aspis_r0_writer_copies.merge_check_loop stable late flag
            (Usize.wrapping_add i 1#usize) =
          R0WriterCopies.merge_check_loop stable late flag (Usize.wrapping_add i 1#usize) := by
        intro flag
        exact ih (16384-(Usize.wrapping_add i 1#usize).val) (by omega)
          flag (Usize.wrapping_add i 1#usize) (by omega) rfl
      simp only [hnext]
    · simp only [if_neg (show ¬i < 16384#usize by simpa [UScalar.lt_equiv] using hit)]

theorem check (stable late : Bank) :
    AspisBuilderGlueSource.aspis_r0_writer_copies.merge_check stable late =
      R0WriterCopies.merge_check stable late :=
  check_loop stable late true 0#usize (by simp)

#print axioms source_count
#print axioms model_count
#print axioms copy_loop
#print axioms copy
#print axioms check_loop
#print axioms check
end R1Z.BuilderBankMerge
