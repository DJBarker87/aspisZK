import S6NativeDigestAcceptedInverseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeDigestEncodeSourceEq
open AspisR1TerminalDecoder

theorem encode_eq (digest : Array U32 8#usize) :
    atomic_statement.encode_digest_canonical digest=
      AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical digest := by
  obtain ⟨output,run,contents⟩ := spec_imp_exists (AspisS6SourceCodec.DigestContents.encode_contents digest)
  rw [run,AspisR1.S2K.DigestBytes.exact]
  have same : AspisR1.S2K.DigestBytes.bytes digest=output := by
    apply Subtype.ext
    exact (AspisS6NativeAfterstateEncoderReuse.native_digest_bytes digest).trans contents.symm
  rw [same]

@[step] theorem reference_inverse_spec (bytes : Array U8 32#usize) :
    atomic_statement.decode_digest_canonical bytes
      ⦃ result => ∀ digest, result=core.result.Result.Ok digest →
        AspisS6SourceCodec.aspis_statement.atomic_statement.encode_digest_canonical digest=ok bytes ⦄ := by
  have inverse := AspisS6NativeDigestAcceptedInverse.inverse_spec bytes
  simpa only [encode_eq] using inverse

#print axioms encode_eq
#print axioms reference_inverse_spec
end AspisS6NativeDigestEncodeSourceEq
