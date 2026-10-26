import F3K_ScalarJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_RhoJoin
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem rho {Hash : Type} (D : aspis_core.Digest32 Hash) (B : PreparedModel.Boundaries)
    (before after : transcript.Transcript Hash) (payload : Slice U8)
    (value : aspis_core.field.QM31)
    (success : PreparedModel.scalar_k B D before 32#u8 payload=ok (value,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (frame : rowBytes p 32=framed (MultiproofConeCanonical.bytesOf payload.val))
    (fits : payload.val.length<4294967296) (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    (eval H (LiteralByteSampler.samp 32 P (F3J_InputRows.proof p root w bound 32)).toProgram).1=
      observe (run (PreparedScalarEffects.scalar_k effects B D before 32#u8 payload)).1 ∧
    (eval H (LiteralByteSampler.samp 32 P (F3J_InputRows.proof p root w bound 32)).toProgram).2.2=decodeState after.state := by
  obtain ⟨block,call,sampled⟩ := PAln_OpeningCalls.rho_success B D before after 32#u8 payload value success
  have joined := F3J_OpeningJoin.block D before after 32#u8 payload block call H backend p root w bound
    (by right;right;right;right;rfl) frame fits P state
  rw [F3J_ScalarCode.rho D B before after 32#u8 payload block call]
  exact joined

#print axioms rho
end AspisR1.F3K_RhoJoin
end
