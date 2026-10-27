import RPz7_F3L_SamplerAt
import RPz7_F3L_RhoChallenge
import RPz7_F3K_PayloadFits
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_RhoEntry
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem entry {Hash : Type} (D : aspis_core.Digest32 Hash) (B : PreparedModel.Boundaries)
    (before after : transcript.Transcript Hash) (payload : Slice U8) (out : aspis_core.field.QM31)
    (success : PreparedModel.scalar_k B D before 32#u8 payload=ok (out,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (frame : rowBytes p 32=framed (MultiproofConeCanonical.bytesOf payload.val))
    (P : LiteralTranscript.Prefix) (length : P.rounds.length=32)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    (eval H (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) 32 1 P)).2.rounds[32]?=
      some (F3J_InputRows.proof p root w bound 32,
        (TranscriptView.Value.ordinary (LiteralOpeningView.eK (F3L_RhoMeaning.decode out)),decodeState after.state)) := by
  have e := F3K_SamplerIndex.first_entry H (F3J_InputRows.proof p root w bound) 32 0 P
  rw [length] at e
  have value := F3L_RhoChallenge.value D B before after payload out success H backend p root w bound
    frame (F3K_PayloadFits.fits payload _ frame (bound 32)) P state
  exact e.trans (congrArg (fun c => some (F3J_InputRows.proof p root w bound 32,c)) value)

#print axioms entry
end AspisR1.F3L_RhoEntry
end
