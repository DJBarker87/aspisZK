import F3J_OpeningSampler
import F3J_LengthFrame
import F3J_ScalarCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3J_OpeningJoin
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
open AspisR1PublicPreparation PreparedHashCode OraclePortCompactDraft

theorem block {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8)
    (value : Array U8 32#usize)
    (success : transcript.Transcript.block D before row payload=ok (value,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (schedule : row.val=27 ∨ row.val=28 ∨ row.val=29 ∨ row.val=30 ∨ row.val=32)
    (frame : rowBytes p row.val=framed (MultiproofConeCanonical.bytesOf payload.val))
    (fits : payload.val.length<4294967296)
    (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    let pf := F3J_InputRows.proof p root w bound
    (eval H (LiteralByteSampler.samp row.val P (pf row.val)).toProgram).1=
      observe (run (PreparedHashEffects.block effects D before row payload)).1 ∧
    (eval H (LiteralByteSampler.samp row.val P (pf row.val)).toProgram).2.2=decodeState after.state := by
  obtain ⟨c⟩ := F3J_OpeningFacts.from_success D before after row payload value success
  have model := F3J_OpeningSampler.payload c H backend (by omega) (by omega) (by omega) (by omega)
    P (F3J_InputRows.proof p root w bound row.val) ⟨rowBytes p row.val,bound row.val⟩
    (by rw [F3J_InputRows.erased,if_neg (by omega)]) state
    (frame.trans (F3J_LengthFrame.framed payload fits))
  have source := F3J_OpeningCode.block c
  exact ⟨(congrArg Prod.fst model).trans source.symm,congrArg (fun r => r.2.2) model⟩

#print axioms block
end AspisR1.F3J_OpeningJoin
end
