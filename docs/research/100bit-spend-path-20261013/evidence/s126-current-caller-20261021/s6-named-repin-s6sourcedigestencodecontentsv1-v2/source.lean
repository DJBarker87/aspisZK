import S6SourceDigestTotalV1
import S6EightChunkFrameV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.DigestContents
open AspisS6FiveUnrolledCodec

def chunks (digest : Array U32 8#usize) : List U8 :=
  (core.num.U32.to_le_bytes (digest.val[0]'(by rw [digest.property]; decide))).val ++
  (core.num.U32.to_le_bytes (digest.val[1]'(by rw [digest.property]; decide))).val ++
  (core.num.U32.to_le_bytes (digest.val[2]'(by rw [digest.property]; decide))).val ++
  (core.num.U32.to_le_bytes (digest.val[3]'(by rw [digest.property]; decide))).val ++
  (core.num.U32.to_le_bytes (digest.val[4]'(by rw [digest.property]; decide))).val ++
  (core.num.U32.to_le_bytes (digest.val[5]'(by rw [digest.property]; decide))).val ++
  (core.num.U32.to_le_bytes (digest.val[6]'(by rw [digest.property]; decide))).val ++
  (core.num.U32.to_le_bytes (digest.val[7]'(by rw [digest.property]; decide))).val

private theorem word_bytes_length (x : U32) :
    (Array.to_slice (core.num.U32.to_le_bytes x)).length=4 := by
  change (core.num.U32.to_le_bytes x).val.length=4
  simpa using (core.num.U32.to_le_bytes x).property

/-- Exact bytes produced by the actual digest encoder, before canonicality. -/
@[step] theorem encode_contents (digest : Array U32 8#usize) :
    aspis_statement.atomic_statement.encode_digest_canonical digest
      ⦃ output => output.val=chunks digest ⦄ := by
  unfold aspis_statement.atomic_statement.encode_digest_canonical
  simp only [aspis_core.field.M31.to_le_bytes,bind_tc_ok]
  step*
  all_goals (simp_all only [word_bytes_length] <;> try omega)
  unfold chunks
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

#print axioms encode_contents
end AspisS6SourceCodec.DigestContents
