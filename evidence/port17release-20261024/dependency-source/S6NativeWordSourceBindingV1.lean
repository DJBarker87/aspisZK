import S6NativeAfterstateEncoderReuseV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeWordSourceBinding
open AspisR1TerminalDecoder

theorem decode_eq (bytes : Array U8 4#usize) :
    aspis_core.field.M31.from_le_bytes bytes=
      AspisS6SourceCodec.aspis_core.field.M31.from_le_bytes bytes := by
  unfold aspis_core.field.M31.from_le_bytes AspisS6SourceCodec.aspis_core.field.M31.from_le_bytes
    aspis_core.field.P AspisS6SourceCodec.aspis_core.field.P
  rfl

theorem encode_eq (value : U32) :
    aspis_core.field.M31.to_le_bytes value=
      AspisS6SourceCodec.aspis_core.field.M31.to_le_bytes value := by
  rfl

@[step] theorem word_spec (bytes : Array U8 4#usize) :
    aspis_core.field.M31.from_le_bytes bytes
      ⦃ result => ∀ value, result=some value →
        aspis_core.field.M31.to_le_bytes value=ok bytes ⦄ := by
  rw [decode_eq]
  have h := AspisS6SourceCodec.DigestDecode.word_spec bytes
  simpa only [encode_eq] using h

#print axioms decode_eq
#print axioms encode_eq
#print axioms word_spec
end AspisS6NativeWordSourceBinding
