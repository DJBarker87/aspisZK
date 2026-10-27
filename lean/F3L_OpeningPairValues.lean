import F3L_GammaEntry
import F3L_OrdinaryEntry
import F3K_OpeningPair27
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_OpeningPairValues
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft
open AspisR1CurrentCaller.BorrowedClaimPrepared
open AspisR1CurrentPreparedClaim.Concrete AspisR1ClaimPreparedBridge
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw
attribute [local irreducible] closedHashBoundaries F3J_InputRows.proof F3J_SamplerRun.program

theorem entries {Hash : Type} {D : aspis_core.Digest32 Hash}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {v : verifier.View} {p : Parsed}
    (c : F3K_OpeningCalls.Calls D closedHashBoundaries.sampling embed v p)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (length : P.rounds.length=27)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.t0.state) :
    let pf := F3J_InputRows.proof p root w bound
    let Q := (eval H (F3J_SamplerRun.program pf 27 6 P)).2
    Q.rounds[27]?=some (pf 27,(TranscriptView.Value.ordinary (decode (toClaimE c.gamma)),decodeState c.t1.state)) ∧
    Q.rounds[28]?=some (pf 28,(TranscriptView.Value.ordinary (decode (toClaimE c.kappa)),decodeState c.t2.state)) := by
  let pf := F3J_InputRows.proof p root w bound
  let P28 := (eval H (F3J_SamplerRun.program pf 27 1 P)).2
  have first := F3K_ScalarOne.scalar D closedHashBoundaries.sampling c.t0 c.t1 27#u8 v.y1 c.gamma true
    c.firstCall H backend p root w bound (by decide) c.frame27
    (F3K_PayloadFits.fits v.y1 _ c.frame27 (bound 27)) P state
  have len28 : P28.rounds.length=28 := by
    have h := F3J_SamplerRun.length H pf 27 1 P
    rw [length] at h
    exact h
  have e27 := F3L_GammaEntry.entry D c.t0 c.t1 27#u8 v.y1 c.gamma c.firstCall H backend
    p root w bound rfl c.frame27 P length 5 state
  have e28 := F3L_OrdinaryEntry.entry D c.t1 c.t2 28#u8 (Array.to_slice c.inactive) c.kappa c.secondCall
    H backend p root w bound (by decide) c.frame28 P28 len28 4 first.2
  have split := F3J_SamplerCompose.value H pf 27 1 5 P
  constructor
  · exact e27
  · exact (congrArg (fun Q : LiteralTranscript.Prefix => Q.rounds[28]?) split).trans e28

#print axioms entries
end AspisR1.F3L_OpeningPairValues
end
