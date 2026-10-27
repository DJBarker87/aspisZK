import RPz7_F3L_SamplerAt
import RPz7_F3L_ClosedOrdinary
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_OrdinaryEntry
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft
open AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] closedHashBoundaries

theorem entry {Hash : Type} (D : aspis_core.Digest32 Hash)
    (before after : transcript.Transcript Hash) (row : U8) (payload : Slice U8) (out : PE)
    (success : PreparedModel.scalar closedHashBoundaries.sampling D before row payload false=ok (out,after))
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (p : Parsed) (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (schedule : row.val=28 ∨ row.val=29 ∨ row.val=30)
    (frame : rowBytes p row.val=framed (MultiproofConeCanonical.bytesOf payload.val))
    (P : LiteralTranscript.Prefix) (length : P.rounds.length=row.val) (tail : Nat)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState before.state) :
    (eval H (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) row.val (tail+1) P)).2.rounds[row.val]?=
      some (F3J_InputRows.proof p root w bound row.val,
        (TranscriptView.Value.ordinary (decode (toClaimE out)),decodeState after.state)) := by
  have e := F3K_SamplerIndex.first_entry H (F3J_InputRows.proof p root w bound) row.val tail P
  rw [length] at e
  have value := F3L_ClosedOrdinary.value D before after row payload out success H backend p root w bound
    schedule frame (F3K_PayloadFits.fits payload _ frame (bound row.val)) P state
  exact e.trans (congrArg (fun c => some (F3J_InputRows.proof p root w bound row.val,c)) value)

#print axioms entry
end AspisR1.F3L_OrdinaryEntry
end
