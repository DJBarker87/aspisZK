import S6SourceDigestRoundtripV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6SourceCodec.DigestRoundtrip
open AspisS6FiveUnrolledCodec

/-- Every accepted complete digest decode re-encodes to exactly its original
32 bytes. The sole premise is the actual decoder return, not independent word
success, canonicality, a byte carrier or an assumed encoder correspondence. -/
theorem accepted_roundtrip (bytes : Array U8 32#usize) (digest : Array U32 8#usize)
    (accepted : aspis_statement.atomic_statement.decode_digest_canonical bytes=
      ok (core.result.Result.Ok digest)) :
    aspis_statement.atomic_statement.encode_digest_canonical digest=ok bytes := by
  have contents := decoded_contents bytes
  rw [accepted,WP.spec_ok] at contents
  have recovered := contents digest rfl
  obtain ⟨output,houtput,hcontents⟩ := spec_imp_exists (DigestContents.encode_contents digest)
  have heq : output=bytes := Subtype.ext (hcontents.trans recovered)
  simpa only [heq] using houtput

@[step] theorem inverse_spec (bytes : Array U8 32#usize) :
    aspis_statement.atomic_statement.decode_digest_canonical bytes
      ⦃ result => ∀ digest, result=core.result.Result.Ok digest →
        aspis_statement.atomic_statement.encode_digest_canonical digest=ok bytes ⦄ := by
  obtain ⟨result,hresult⟩ := DigestDecode.decode_total bytes
  rw [hresult,WP.spec_ok]
  intro digest hd
  exact accepted_roundtrip bytes digest (hresult.trans (congrArg ok hd))

#print axioms accepted_roundtrip
#print axioms inverse_spec
end AspisS6SourceCodec.DigestRoundtrip
