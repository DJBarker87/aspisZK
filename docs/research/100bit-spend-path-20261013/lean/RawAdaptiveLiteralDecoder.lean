import RawLiteralDecoderDensity

/-! A decoder may select the public statement from its current input/table,
without a union over statements. Actual public-selection correctness is a
separate deterministic property, not assumed by the density theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawAdaptiveLiteralDecoder
open FS FS2 R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

abbrev PublicChoice := Bytes → Table Bytes State → Option LiteralTranscript.Public

def decode (pubChoice : PublicChoice) (words : RawLiteralDecoderDensity.WordChoice) :
    Dec LiteralTranscript.Public LiteralTranscript.Message LiteralTranscript.Challenge
      Bytes State (List State) :=
  fun a T => (pubChoice a T).bind fun pub => RawLiteralDecoderDensity.decode words pub a T

theorem density (protocolDecoder : LiteralByteProtocol.Decoder)
    (pubChoice : PublicChoice) (words : RawLiteralDecoderDensity.WordChoice) :
    ChainDensity3 (LiteralByteProtocol.protocol protocolDecoder) LiteralByteProtocol.rows
      (decode pubChoice words) := by
  intro a T own pend g hd
  unfold decode at hd
  cases hp : pubChoice a T with
  | none => simp [hp] at hd
  | some pub =>
      simp only [hp,Option.bind_some] at hd
      exact RawLiteralDecoderDensity.density protocolDecoder words pub a T own pend g hd

theorem decode_of_public (pubChoice : PublicChoice) (words : RawLiteralDecoderDensity.WordChoice)
    (a : Bytes) (T : Table Bytes State) (pub : LiteralTranscript.Public)
    (hp : pubChoice a T = some pub) :
    decode pubChoice words a T = RawLiteralDecoderDensity.decode words pub a T := by
  simp only [decode,hp,Option.bind_some]

#print axioms density
#print axioms decode_of_public
end AspisR1.RawAdaptiveLiteralDecoder
end
