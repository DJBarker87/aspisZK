import RPz7_S6NativeAfterstateEncoderReuseV1
import Mathlib.Tactic.IntervalCases
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativeAfterstateEncoderReuse
open AspisS6SourceCodec

theorem native_digest_bytes (digest : Array U32 8#usize) :
    (AspisR1.S2K.DigestBytes.bytes digest).val=DigestContents.chunks digest := by
  have expanded : digest.val=[(digest.val[0]'(by rw [digest.property]; decide)), (digest.val[1]'(by rw [digest.property]; decide)), (digest.val[2]'(by rw [digest.property]; decide)), (digest.val[3]'(by rw [digest.property]; decide)), (digest.val[4]'(by rw [digest.property]; decide)), (digest.val[5]'(by rw [digest.property]; decide)), (digest.val[6]'(by rw [digest.property]; decide)), (digest.val[7]'(by rw [digest.property]; decide))] := by
    apply List.ext_getElem
    · simp [digest.property]
    · intro i hi hj
      have hi8 : i<8 := by simpa [digest.property] using hi
      interval_cases i <;> rfl
  unfold AspisR1.S2K.DigestBytes.bytes
  rw [expanded]
  simp only [AspisR1.S2K.DigestBytes.fold]
  change ((((((((List.replicate 32 (0#u8)).setSlice! 0 (core.num.U32.to_le_bytes (digest.val[0]'(by rw [digest.property]; decide))).val).setSlice! 4 (core.num.U32.to_le_bytes (digest.val[1]'(by rw [digest.property]; decide))).val).setSlice! 8 (core.num.U32.to_le_bytes (digest.val[2]'(by rw [digest.property]; decide))).val).setSlice! 12 (core.num.U32.to_le_bytes (digest.val[3]'(by rw [digest.property]; decide))).val).setSlice! 16 (core.num.U32.to_le_bytes (digest.val[4]'(by rw [digest.property]; decide))).val).setSlice! 20 (core.num.U32.to_le_bytes (digest.val[5]'(by rw [digest.property]; decide))).val).setSlice! 24 (core.num.U32.to_le_bytes (digest.val[6]'(by rw [digest.property]; decide))).val).setSlice! 28 (core.num.U32.to_le_bytes (digest.val[7]'(by rw [digest.property]; decide))).val=DigestContents.chunks digest
  unfold DigestContents.chunks
  exact AspisS6SliceFrame.eight_chunks 0#u8
    (core.num.U32.to_le_bytes (digest.val[0]'(by rw [digest.property]; decide))).val
    (core.num.U32.to_le_bytes (digest.val[1]'(by rw [digest.property]; decide))).val
    (core.num.U32.to_le_bytes (digest.val[2]'(by rw [digest.property]; decide))).val
    (core.num.U32.to_le_bytes (digest.val[3]'(by rw [digest.property]; decide))).val
    (core.num.U32.to_le_bytes (digest.val[4]'(by rw [digest.property]; decide))).val
    (core.num.U32.to_le_bytes (digest.val[5]'(by rw [digest.property]; decide))).val
    (core.num.U32.to_le_bytes (digest.val[6]'(by rw [digest.property]; decide))).val
    (core.num.U32.to_le_bytes (digest.val[7]'(by rw [digest.property]; decide))).val
    (core.num.U32.to_le_bytes (digest.val[0]'(by rw [digest.property]; decide))).property
    (core.num.U32.to_le_bytes (digest.val[1]'(by rw [digest.property]; decide))).property
    (core.num.U32.to_le_bytes (digest.val[2]'(by rw [digest.property]; decide))).property
    (core.num.U32.to_le_bytes (digest.val[3]'(by rw [digest.property]; decide))).property
    (core.num.U32.to_le_bytes (digest.val[4]'(by rw [digest.property]; decide))).property
    (core.num.U32.to_le_bytes (digest.val[5]'(by rw [digest.property]; decide))).property
    (core.num.U32.to_le_bytes (digest.val[6]'(by rw [digest.property]; decide))).property
    (core.num.U32.to_le_bytes (digest.val[7]'(by rw [digest.property]; decide))).property

#print axioms native_digest_bytes
end AspisS6NativeAfterstateEncoderReuse
