import RPz7_F3L_OrdinaryChallenge
import RPz7_F3L_SamplingSlots
import RPz7_F3J_OpeningJoin
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_ClosedOrdinary
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft
open AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] closedHashBoundaries

theorem value {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8) (out : PE)
    (success : PreparedModel.scalar closedHashBoundaries.sampling D before row payload false=ok (out,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (schedule : row.val=28 ∨ row.val=29 ∨ row.val=30)
    (frame : rowBytes p row.val=framed (MultiproofConeCanonical.bytesOf payload.val))
    (fits : payload.val.length<4294967296) (P : LiteralTranscript.Prefix)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    (eval H (LiteralByteSampler.samp row.val P (F3J_InputRows.proof p root w bound row.val)).toProgram).2=
      (TranscriptView.Value.ordinary (decode (toClaimE out)),decodeState after.state) := by
  obtain ⟨block,call,sampled⟩ := PAln_OpeningCalls.scalar_success closedHashBoundaries.sampling
    D before after row payload false out success
  simp only [Bool.false_eq_true,if_false] at sampled
  rw [F3L_SamplingSlots.ordinary] at sampled
  obtain ⟨c⟩ := F3J_OpeningFacts.from_success D before after row payload block call
  apply F3L_OrdinaryChallenge.value c out sampled H backend schedule P _
    ⟨rowBytes p row.val,bound row.val⟩
  · rw [F3J_InputRows.erased,if_neg (by omega)]
  · exact state
  · exact frame.trans (F3J_LengthFrame.framed payload fits)

#print axioms value
end AspisR1.F3L_ClosedOrdinary
end
