import F3L_MatchingFromEntries
import F3L_OpeningPairValues
import F3L_OpeningAlphaValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_OpeningDataFields
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft OraclePortStoredDecisionDraftC4
open AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] closedHashBoundaries F3J_InputRows.proof F3J_SamplerRun.program

theorem fields {Hash : Type} {D : aspis_core.Digest32 Hash}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {v : verifier.View} {p : Parsed}
    (c : F3K_OpeningCalls.Calls D closedHashBoundaries.sampling embed v p)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (length : P.rounds.length=27)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.t0.state)
    (q : Fin 22 → Fin 262144) (d : MatchingSupport.Data LiteralTranscript.E)
    (read : LiteralMatchingData.read (typedRows p q (LiteralTranscript.erasePrefix (eval H
      (F3J_SamplerRun.program (F3J_InputRows.proof p root w bound) 27 6 P)).2))=some d) :
    d.gamma=decode (toClaimE c.gamma) ∧ d.kappa=decode (toClaimE c.kappa) ∧
    d.alpha0=decode (toClaimE c.alpha0) ∧ d.alpha1=decode (toClaimE c.alpha1) := by
  have pair := F3L_OpeningPairValues.entries c H backend root w bound P length state
  have alpha := F3L_OpeningAlphaValues.entries c H backend root w bound P length state
  apply F3L_MatchingFromEntries.fields p q _ d
    (fun j=>F3J_InputRows.proof p root w bound (27+j.val))
    ![decode (toClaimE c.gamma),decode (toClaimE c.kappa),decode (toClaimE c.alpha0),decode (toClaimE c.alpha1)]
    ![decodeState c.t1.state,decodeState c.t2.state,decodeState c.t3.state,decodeState c.t4.state] _ read
  intro j
  fin_cases j
  · exact pair.1
  · exact pair.2
  · exact alpha.1
  · exact alpha.2

#print axioms fields
end AspisR1.F3L_OpeningDataFields
end
