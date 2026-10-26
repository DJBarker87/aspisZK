import F3L_GammaMeaning
import F3J_OpeningSampler
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_GammaChallenge
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge

theorem value {Hash : Type} {D : aspis_core.Digest32 Hash}
    {before after : transcript.Transcript Hash} {row : U8} {payload : Slice U8}
    {block : Array U8 32#usize} (c : F3J_OpeningFacts.Calls D before after row payload block)
    (out : PE) (sampled : candidateGammaPublic block=ok out)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (schedule : row.val=27)
    (P : LiteralTranscript.Prefix) (m : LiteralTranscript.Message) (b : LiteralTranscript.BytesMessage)
    (erased : LiteralTranscript.erase m=.payload b)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state)
    (frame : b.val=PublicInitFrame.lengthBytes (UScalar.cast .U32 (Slice.len payload)).val++SourceDigestAddresses.rawBytes payload) :
    (eval H (LiteralByteSampler.samp row.val P m).toProgram).2=
      (TranscriptView.Value.ordinary (decode (toClaimE out)),decodeState after.state) := by
  have full := F3J_OpeningSampler.payload c H backend (by omega) (by omega) (by omega)
    (by omega) P m b erased state frame
  rw [full]
  have sigma : SelectedTranscriptParams.params.σ row.val (decodeState block)=
      R0C.ModuloField.gamma (decodeState block) := by
    simp only [SelectedTranscriptParams.params_sigma,SelectedChallengeMap.sigma,
      if_pos schedule]
  rw [sigma,F3L_GammaMeaning.value block out sampled]

#print axioms value
end AspisR1.F3L_GammaChallenge
end
