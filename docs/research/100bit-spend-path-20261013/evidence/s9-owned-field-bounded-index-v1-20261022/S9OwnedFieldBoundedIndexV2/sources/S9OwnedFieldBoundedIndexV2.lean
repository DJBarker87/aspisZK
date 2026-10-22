import S9OwnedFieldReaderReadbackV1
import WeightsFieldSuccess
import AspisV8R19.R152WrappingBounds

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace AspisR1S9OwnedFieldBoundedIndexV1

open AspisR1S9OwnedFieldReaderReadbackV1
open AspisR1WeightsFieldCurrent.WeightsFieldSuccess
open AspisV8R19.R152WrappingBounds

/-- The protocol bound (48 fields) is far below the Usize ceiling, so all
three byte-offset calculations in `weights.field` are ordinary checked
operations, equal to the emitted wrapping operations. -/
theorem field_offsets_fit_usize (i : Usize) (hi : i.val < 48) :
    i.val * 32 ≤ Usize.max ∧
    i.val + 1 ≤ Usize.max ∧
    (i.val + 1) * 32 ≤ Usize.max := by
  have hcap : 1536 ≤ Usize.max := by
    scalar_tac
  constructor
  · have hsmall : i.val * 32 ≤ 48 * 32 := by omega
    omega
  constructor
  · omega
  · have hsmall : (i.val + 1) * 32 ≤ 48 * 32 := by omega
    omega

/-- Generic index-bounded bridge. The bound is the only protocol premise;
the bridge proves, rather than assumes, both offset and successor
correspondence. -/
theorem checked_offsets_eq_owned_wrapping (i : Usize) (hi : i.val < 48) :
    (i * 32#usize : Result Usize) =
        .ok (Std.Usize.wrapping_mul i 32#usize) ∧
    (i + 1#usize : Result Usize) =
        .ok (Std.Usize.wrapping_add i 1#usize) ∧
    (Std.Usize.wrapping_add i 1#usize * 32#usize : Result Usize) =
        .ok (Std.Usize.wrapping_mul (Std.Usize.wrapping_add i 1#usize) 32#usize) := by
  obtain ⟨hstart, hnext, hfinish⟩ := field_offsets_fit_usize i hi
  have h32 : (32#usize : Usize).val = 32 := rfl
  have hone : (1#usize : Usize).val = 1 := rfl
  have hmul0 := checked_mul_eq_wrapping i 32#usize (by simpa [h32] using hstart)
  have hadd := checked_add_eq_wrapping i 1#usize (by simpa [hone] using hnext)
  have hmul1 := checked_mul_eq_wrapping (Std.Usize.wrapping_add i 1#usize)
      32#usize (by
        rw [Std.Usize.wrapping_add_val_eq]
        have hsize : Usize.max + 1 = UScalar.size .Usize := by
          simp [Usize.max, Usize.size, Usize.numBits]
        have hlt : i.val + 1 < UScalar.size .Usize := by omega
        rw [hone, h32, Nat.mod_eq_of_lt hlt]
        exact hfinish)
  exact ⟨hmul0, hadd, hmul1⟩

/-- A bounded successful owned reader is also a successful call of the
generic checked decoder on the very same bytes and decoder. This is the
source-level operation bridge; callers still supply the concrete bound. -/
theorem owned_reader_eq_checked_reader
    (bytes : Slice U8) (i : Usize) (hi : i.val < 48) :
    AspisR1S9FieldOwnedV1.weights.field bytes i =
      AspisR1WeightsFieldCurrent.weights.field
        AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes bytes i := by
  unfold AspisR1S9FieldOwnedV1.weights.field
    AspisR1WeightsFieldCurrent.weights.field
  obtain ⟨hstart, hnext, hfinish⟩ := checked_offsets_eq_owned_wrapping i hi
  simp only [hstart, hnext, hfinish, lift, bind_tc_ok]

/-- Successful selected bytes are therefore precisely the generic checked
decoder's selected bytes; in particular the existing checked-slice theorem
applies with no extra reader-success premise. -/
theorem owned_reader_success_checked_slice
    (bytes : Slice U8) (i : Usize) (out : AspisR1S9OwnedFromLimbsMapV1.C)
    (hi : i.val < 48)
    (h : AspisR1S9FieldOwnedV1.weights.field bytes i = .ok out) :
    ∃ start next finish selected,
      (i * 32#usize : Result Usize) = .ok start ∧
      (i + 1#usize : Result Usize) = .ok next ∧
      (next * 32#usize : Result Usize) = .ok finish ∧
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice U8) bytes
        { start := start, «end» := finish } = .ok selected ∧
      AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes selected =
        .ok (some out) := by
  rw [owned_reader_eq_checked_reader bytes i hi] at h
  exact checked_slice_decode
    AspisR1S9FieldOwnedV1.field.wide_exact.WideExact.from_le_bytes
    bytes i out h

#print axioms field_offsets_fit_usize
#print axioms checked_offsets_eq_owned_wrapping
#print axioms owned_reader_eq_checked_reader
#print axioms owned_reader_success_checked_slice

end AspisR1S9OwnedFieldBoundedIndexV1
