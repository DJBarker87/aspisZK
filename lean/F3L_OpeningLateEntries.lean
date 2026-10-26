import F3L_RhoEntry
import F3K_OpeningFirst4
import F3K_QueryOne
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3L_OpeningLateEntries
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw

theorem entries {Hash : Type} {D : aspis_core.Digest32 Hash} {B : PreparedModel.Boundaries}
    {embed : aspis_core.field.M31 → Result aspis_core.field.WideExact}
    {v : verifier.View} {p : Parsed} (c : F3K_OpeningCalls.Calls D B embed v p)
    (H : Bytes → State) (backend : Tx1DigestLog.ByteOracleBackend D H)
    (root : State) (w : CanonicalCutEnrichedTranscript.Words)
    (bound : ∀ row,(rowBytes p row).length≤SelectedTranscriptParams.D)
    (P : LiteralTranscript.Prefix) (length : P.rounds.length=27)
    (state : UnifiedSampler.stateOf SelectedTranscriptParams.params (LiteralTranscript.erasePrefix P)=decodeState c.t0.state) :
    let pf := F3J_InputRows.proof p root w bound
    let Q := (eval H (F3J_SamplerRun.program pf 27 6 P)).2
    Q.rounds[31]?=some (pf 31,
      (TranscriptView.Value.queries (.ok (c.queries.val.map (fun x=>x.val))),decodeState c.t5.state)) ∧
    Q.rounds[32]?=some (pf 32,
      (TranscriptView.Value.ordinary (LiteralOpeningView.eK (F3L_RhoMeaning.decode c.rho)),decodeState c.t6.state)) := by
  let pf := F3J_InputRows.proof p root w bound
  let P31 := (eval H (F3J_SamplerRun.program pf 27 4 P)).2
  let P32 := (eval H (F3J_SamplerRun.program pf 31 1 P31)).2
  have first := F3K_OpeningFirst4.sampler c H backend root w bound P state
  have len31 : P31.rounds.length=31 := by
    have h := F3J_SamplerRun.length H pf 27 4 P
    rw [length] at h
    exact h
  have len32 : P32.rounds.length=32 := by
    have h := F3J_SamplerRun.length H pf 31 1 P31
    rw [len31] at h
    exact h
  have query := F3K_QueryFull.exact_row D embed c.t4 c.t5 v.final_message c.queries c.queryCall
    H backend (F3K_PayloadFits.fits v.final_message _ c.frame31 (bound 31))
    P31 (pf 31) ⟨rowBytes p 31,bound 31⟩
    (by rw [F3J_InputRows.erased,if_neg (by decide)]) first.2 c.frame31
  have entry31 := F3K_SamplerIndex.first_entry H pf 31 1 P31
  rw [len31,congrArg Prod.snd query] at entry31
  have qstate := (F3K_QueryOne.sampler c H backend root w bound P31 first.2).2
  have entry32 := F3L_RhoEntry.entry D B c.t5 c.t6 PreparedScratchReachability.emptyPayload c.rho
    c.rhoCall H backend p root w bound c.frame32 P32 len32 qstate
  have split4 := F3J_SamplerCompose.value H pf 27 4 2 P
  have split1 := F3J_SamplerCompose.value H pf 31 1 1 P31
  constructor
  · exact (congrArg (fun Q : LiteralTranscript.Prefix => Q.rounds[31]?) split4).trans entry31
  · exact (congrArg (fun Q : LiteralTranscript.Prefix => Q.rounds[32]?) split4).trans
      ((congrArg (fun Q : LiteralTranscript.Prefix => Q.rounds[32]?) split1).trans entry32)

#print axioms entries
end AspisR1.F3L_OpeningLateEntries
end
