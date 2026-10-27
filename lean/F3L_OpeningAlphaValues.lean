import F3L_OrdinaryEntry
import F3K_OpeningPair27
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_OpeningAlphaValues
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
    Q.rounds[29]?=some (pf 29,(TranscriptView.Value.ordinary (decode (toClaimE c.alpha0)),decodeState c.t3.state)) ∧
    Q.rounds[30]?=some (pf 30,(TranscriptView.Value.ordinary (decode (toClaimE c.alpha1)),decodeState c.t4.state)) := by
  let pf := F3J_InputRows.proof p root w bound
  let P29 := (eval H (F3J_SamplerRun.program pf 27 2 P)).2
  let P30 := (eval H (F3J_SamplerRun.program pf 29 1 P29)).2
  have first := F3K_OpeningPair27.sampler c H backend root w bound P state
  have len29 : P29.rounds.length=29 := by
    have h := F3J_SamplerRun.length H pf 27 2 P
    rw [length] at h
    exact h
  have len30 : P30.rounds.length=30 := by
    have h := F3J_SamplerRun.length H pf 29 1 P29
    rw [len29] at h
    exact h
  have third := F3K_ScalarOne.scalar D closedHashBoundaries.sampling c.t2 c.t3 29#u8 v.round0 c.alpha0 false
    c.thirdCall H backend p root w bound (by decide) c.frame29
    (F3K_PayloadFits.fits v.round0 _ c.frame29 (bound 29)) P29 first.2
  have e29 := F3L_OrdinaryEntry.entry D c.t2 c.t3 29#u8 v.round0 c.alpha0 c.thirdCall H backend
    p root w bound (by decide) c.frame29 P29 len29 3 first.2
  have e30 := F3L_OrdinaryEntry.entry D c.t3 c.t4 30#u8 c.second.deref c.alpha1 c.fourthCall H backend
    p root w bound (by decide) c.frame30 P30 len30 2 third.2
  have split2 := F3J_SamplerCompose.value H pf 27 2 4 P
  have split1 := F3J_SamplerCompose.value H pf 29 1 3 P29
  constructor
  · exact (congrArg (fun Q : LiteralTranscript.Prefix => Q.rounds[29]?) split2).trans e29
  · exact (congrArg (fun Q : LiteralTranscript.Prefix => Q.rounds[30]?) split2).trans
      ((congrArg (fun Q : LiteralTranscript.Prefix => Q.rounds[30]?) split1).trans e30)

#print axioms entries
end AspisR1.F3L_OpeningAlphaValues
end
