import R13ClosePadding
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1Stage2.R13Close.Padding

/-- Propagate the actual checked byte-count multiplication and suffix read
into the scanner's divisibility premise. Slot width is explicit until the
compact::slot refinement is connected. -/
theorem source_tail_mod (stored tail : Slice U8) (count cut : Usize) (capacity : Nat)
    (hslot : stored.val.length = 32 * capacity)
    (hmul : 32#usize * count = ok cut)
    (hread : core.slice.index.Slice.index
      (core.slice.index.SliceIndexRangeFromUsizeSlice U8) stored
      {start := cut} = ok tail) : tail.val.length % 8 = 0 := by
  have hm := UScalar.mul_equiv 32#usize count
  change (32#usize).mul count = ok cut at hmul
  rw [hmul] at hm
  have hcut : cut.val = 32 * count.val := by simpa using hm.2.1
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeFromUsizeSlice,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index] at hread
  split at hread
  · have he := Result.ok.inj hread
    have hv := congrArg (fun s : Slice U8 => s.val.length) he
    have hl : tail.val.length = stored.val.length - cut.val := by
      simpa [List.slice] using hv.symm
    rw [hl, hslot, hcut]
    exact slot_tail_mod capacity count.val
  · cases hread

#print axioms source_tail_mod
end AspisR1Stage2.R13Close.Padding
