import F3J_QueryJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_QueryAddress
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation SourceDigestAddresses
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

theorem address (before : Array U8 32#usize) (payload : Slice U8)
    (fits : payload.val.length<4294967296)
    (P : LiteralTranscript.Prefix) (b : LiteralTranscript.BytesMessage)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before)
    (framing : b.val=OraclePortCompactDraft.framed (MultiproofConeCanonical.bytesOf payload.val)) :
    (UnifiedSampler.absorb SelectedTranscriptParams.params 31 (LiteralTranscript.erasePrefix P) b).toBytes=
      flatten (CallerStep.openingAbsorbParts before 191#u8
        (UScalar.cast .U32 (Slice.len payload)) payload) := by
  unfold UnifiedSampler.absorb
  rw [state,absorbA,AspisV8R19.DuplexFrames.Addr.toBytes_ofBytes,F3J_OpeningFrame.absorb]
  change AspisV8R19.DuplexFrames.absorb (bytes (decodeState before)) (decodeByte (191#u8)) b.val=_
  rw [framing,F3J_LengthFrame.framed payload fits]
  rfl

#print axioms address
end AspisR1.F3K_QueryAddress
end
