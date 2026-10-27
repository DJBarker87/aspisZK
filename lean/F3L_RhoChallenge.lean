import F3L_RhoMeaning
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_RhoChallenge
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem value {Hash : Type} (D : aspis_core.Digest32 Hash) (B : PreparedModel.Boundaries)
    (before after : transcript.Transcript Hash) (payload : Slice U8) (out : aspis_core.field.QM31)
    (success : PreparedModel.scalar_k B D before 32#u8 payload=ok (out,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (frame : rowBytes p 32=framed (MultiproofConeCanonical.bytesOf payload.val))
    (fits : payload.val.length<4294967296) (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    (eval H (LiteralByteSampler.samp 32 P (F3J_InputRows.proof p root w bound 32)).toProgram).2=
      (TranscriptView.Value.ordinary (LiteralOpeningView.eK (F3L_RhoMeaning.decode out)),decodeState after.state) := by
  obtain ⟨block,call,sampled⟩ := PAln_OpeningCalls.rho_success B D before after 32#u8 payload out success
  obtain ⟨c⟩ := F3J_OpeningFacts.from_success D before after 32#u8 payload block call
  have full := F3J_OpeningSampler.payload c H backend (by decide) (by decide) (by decide)
    (by decide) P (F3J_InputRows.proof p root w bound 32) ⟨rowBytes p 32,bound 32⟩
    (by rw [F3J_InputRows.erased,if_neg (by decide)]) state
    (frame.trans (F3J_LengthFrame.framed payload fits))
  change eval H (LiteralByteSampler.samp 32 P (F3J_InputRows.proof p root w bound 32)).toProgram = _ at full
  exact (congrArg Prod.snd full).trans (congrArg
    (fun x => (TranscriptView.Value.ordinary x,decodeState after.state))
    (F3L_RhoMeaning.value block out sampled).symm)

#print axioms value
end AspisR1.F3L_RhoChallenge
end
