import S6NativeDigestDecodeBindingV1
import S6NativeDigestByteContentsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
open scoped AspisR1TerminalDecoder
namespace AspisS6NativeDigestAcceptedInverse
open AspisR1TerminalDecoder

@[step] theorem decoded_contents (bytes : Array U8 32#usize) :
    atomic_statement.decode_digest_canonical bytes
      ⦃ result => ∀ digest, result=core.result.Result.Ok digest →
        AspisS6SourceCodec.DigestContents.chunks digest=bytes.val ⦄ := by
  unfold atomic_statement.decode_digest_canonical
  step*
  all_goals (intro digest hd; cases hd)
  all_goals (cases r <;> simp_all [AspisS6SourceCodec.DigestContents.chunks,aspis_core.field.M31.to_le_bytes,Array.make])
  all_goals (cases r1 <;> simp_all [AspisS6SourceCodec.DigestContents.chunks,aspis_core.field.M31.to_le_bytes,Array.make])
  all_goals (cases r2 <;> simp_all [AspisS6SourceCodec.DigestContents.chunks,aspis_core.field.M31.to_le_bytes,Array.make])
  all_goals (cases r3 <;> simp_all [AspisS6SourceCodec.DigestContents.chunks,aspis_core.field.M31.to_le_bytes,Array.make])
  all_goals (cases r4 <;> simp_all [AspisS6SourceCodec.DigestContents.chunks,aspis_core.field.M31.to_le_bytes,Array.make])
  all_goals (cases r5 <;> simp_all [AspisS6SourceCodec.DigestContents.chunks,aspis_core.field.M31.to_le_bytes,Array.make])
  all_goals (cases r6 <;> simp_all [AspisS6SourceCodec.DigestContents.chunks,aspis_core.field.M31.to_le_bytes,Array.make])
  all_goals (cases r7 <;> simp_all [AspisS6SourceCodec.DigestContents.chunks,aspis_core.field.M31.to_le_bytes,Array.make])
  all_goals exact AspisS6SourceCodec.DigestRoundtrip.bytes_expansion bytes


theorem accepted_inverse (bytes : Array U8 32#usize) (digest : Array U32 8#usize)
    (accepted : atomic_statement.decode_digest_canonical bytes=ok (core.result.Result.Ok digest)) :
    atomic_statement.encode_digest_canonical digest=ok bytes := by
  have frames := decoded_contents bytes
  rw [accepted,WP.spec_ok] at frames
  have contents := frames digest rfl
  have payload : AspisR1.S2K.DigestBytes.bytes digest=bytes := by
    apply Subtype.ext
    exact (AspisS6NativeAfterstateEncoderReuse.native_digest_bytes digest).trans contents
  rw [AspisR1.S2K.DigestBytes.exact,payload]

@[step] theorem inverse_spec (bytes : Array U8 32#usize) :
    atomic_statement.decode_digest_canonical bytes
      ⦃ result => ∀ digest, result=core.result.Result.Ok digest →
        atomic_statement.encode_digest_canonical digest=ok bytes ⦄ := by
  obtain ⟨result,run,_⟩ := spec_imp_exists (AspisS6NativeDigestDecodeBinding.decode_spec bytes)
  rw [run,WP.spec_ok]
  intro digest accepted
  exact accepted_inverse bytes digest (run.trans (congrArg ok accepted))

#print axioms decoded_contents
#print axioms accepted_inverse
#print axioms inverse_spec
end AspisS6NativeDigestAcceptedInverse
