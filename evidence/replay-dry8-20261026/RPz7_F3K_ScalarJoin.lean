import RPz7_F3J_OpeningJoin
import RPz7_PAln_OpeningCalls
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3K_ScalarJoin
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation PreparedHashCode OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem scalar {Hash : Type} (D : aspis_core.Digest32 Hash) (B : PreparedModel.Boundaries)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (value : aspis_core.field.WideExact) (nonzero : Bool)
    (success : PreparedModel.scalar B D before row payload nonzero=ok (value,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (schedule : row.val=27 ∨ row.val=28 ∨ row.val=29 ∨ row.val=30)
    (frame : rowBytes p row.val=framed (MultiproofConeCanonical.bytesOf payload.val))
    (fits : payload.val.length<4294967296) (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    (eval H (LiteralByteSampler.samp row.val P (F3J_InputRows.proof p root w bound row.val)).toProgram).1=
      observe (run (PreparedScalarEffects.scalar effects B D before row payload nonzero)).1 ∧
    (eval H (LiteralByteSampler.samp row.val P (F3J_InputRows.proof p root w bound row.val)).toProgram).2.2=decodeState after.state := by
  obtain ⟨block,call,sampled⟩ := PAln_OpeningCalls.scalar_success B D before after row payload nonzero value success
  have joined := F3J_OpeningJoin.block D before after row payload block call H backend p root w bound
    (by rcases schedule with h|h|h|h <;> simp only [h,or_true,true_or]) frame fits P state
  rw [F3J_ScalarCode.scalar D B before after row payload block nonzero call]
  exact joined

#print axioms scalar
end AspisR1.F3K_ScalarJoin
end
