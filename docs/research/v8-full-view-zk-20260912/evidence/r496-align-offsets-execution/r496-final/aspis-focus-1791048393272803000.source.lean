import AspisR490AlignOffsets.Funs
import AspisV8R19.R489WordArithmetic

set_option autoImplicit false

/-! Candidate proof against the exact generated `align_to_offsets` body from
R490f. This file is intentionally uncompiled until the lead verifies that the
R497-generated Funs and dependency imports compile. -/
namespace AspisV8R19.R496AlignOffsetsExecution

open Aeneas Aeneas.Std Result

theorem align_to_offsets_complete (xs : Slice U8) :
    ∃ q r : Usize,
      AspisR490AlignOffsets.core.slice.SliceU8.align_to_offsets_mono_4c96ec488904b27cff1cab4fcd1cc6b4 xs =
        .ok (q, r) ∧
      q.val = xs.length / 4 ∧
      r.val = xs.length % 4 ∧
      q.val * 4 + r.val = xs.length ∧
      r.val < 4 := by
  obtain ⟨q, hdiv, hq⟩ := R489WordArithmetic.div_four (Slice.len xs)
  obtain ⟨r, hrem, hr⟩ := R489WordArithmetic.rem_four (Slice.len xs)
  have hmul := R489WordArithmetic.wrapping_mul_one q
  have hpart := R489WordArithmetic.div_rem_partition (Slice.len xs)
  refine ⟨q, r, ?_, ?_, ?_, ?_, ?_⟩
  · simp [AspisR490AlignOffsets.core.slice.SliceU8.align_to_offsets_mono_4c96ec488904b27cff1cab4fcd1cc6b4,
      AspisR490AlignOffsets.core.mem.SizedTypeProperties.SIZE.default_mono_e9319eea2781deb4b1add44e36347b0b,
      AspisR490AlignOffsets.core.mem.SizedTypeProperties.SIZE.default_mono_28ce8d95b2593a4923576aa3ad2ebabc,
      Aeneas.Std.Usize.div, Aeneas.Std.Usize.rem,
      R489WordArithmetic.div_four_one,
      R489WordArithmetic.div_one_one,
      hdiv, hmul, hrem, lift, bind_tc_ok]
  · simpa only [Slice.len_val, Slice.length] using hq
  · simpa only [Slice.len_val, Slice.length] using hr
  · simpa only [hq, hr, Slice.len_val, Slice.length] using hpart.1
  · simpa only [hr, Slice.len_val, Slice.length] using hpart.2

#print axioms align_to_offsets_complete
#print axioms AspisR490AlignOffsets.core.slice.SliceU8.align_to_offsets_mono_4c96ec488904b27cff1cab4fcd1cc6b4
#print axioms AspisR490AlignOffsets.core.mem.SizedTypeProperties.SIZE.default_mono_e9319eea2781deb4b1add44e36347b0b
#print axioms AspisR490AlignOffsets.core.mem.SizedTypeProperties.SIZE.default_mono_28ce8d95b2593a4923576aa3ad2ebabc

end AspisV8R19.R496AlignOffsetsExecution
