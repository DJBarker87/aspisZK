import R1UnifiedRecordCompletion
import R1UnifiedContinuation

/-! Symbolic query and rho-row views of a deterministic unified run.
The connection to a completed transcript prefix is proved only through the
explicit row-zero premises in `UnifiedRecordCompletion`. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedQueryRun

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}

def queryAddress (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) : Addr L :=
  UnifiedSampler.absorb p 31
    (UnifiedRun.transcript p hD H pub c1 payload 31) (payload 31)

def queryResult (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) : AspisV8R19.Q22SamplerProgram.Result :=
  QueryFirstRead.result p H
    (QuerySampler.state p H (H (queryAddress p hD H pub c1 payload)))

def rhoAddress (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) : Addr L :=
  UnifiedSampler.absorb p 32
    (UnifiedRun.transcript p hD H pub c1 payload 32) (payload 32)

theorem query_challenge (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    UnifiedRun.challenge p hD H pub c1 payload 31 =
      UnifiedSampler.liftQuery (queryResult p hD H pub c1 payload) := by
  change (eval H (UnifiedSampler.samp p hD 31
    (UnifiedRun.transcript p hD H pub c1 payload 31)
    (.payload (payload 31))).toProgram).2 = _
  rw [UnifiedSampler.row_query, QuerySamplerBridge.output]
  rfl

theorem query_state (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    UnifiedRun.state p hD H pub c1 payload 32 =
      (queryResult p hD H pub c1 payload).2 := by
  rw [UnifiedRun.state_succ, query_challenge]
  rfl

theorem rho_address (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    rhoAddress p hD H pub c1 payload =
      absorbA p (queryResult p hD H pub c1 payload).2
        (p.lbl 32) (p.enc (payload 32)) (p.encLen (payload 32)) := by
  change absorbA p (UnifiedRun.state p hD H pub c1 payload 32)
      (p.lbl 32) (p.enc (payload 32)) (p.encLen (payload 32)) = _
  rw [query_state]

theorem rho_challenge (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    UnifiedRun.challenge p hD H pub c1 payload 32 =
      TranscriptView.liftChallenge
        (p.σ 32 (H (squeezeA p (H (rhoAddress p hD H pub c1 payload)))),
          H (advanceA p (H (rhoAddress p hD H pub c1 payload)))) := by
  change (eval H (UnifiedSampler.samp p hD 32
    (UnifiedRun.transcript p hD H pub c1 payload 32)
    (.payload (payload 32))).toProgram).2 = _
  rw [UnifiedSampler.row_rho, DuplexSamplers.plain_eval]
  rfl

theorem prefix32 (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M)
    (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord) :
    TranscriptView.withQuery c1
      (completeRounds p emptyTable H 0
        (UnifiedRecords.records p hD H pub c1 payload 31))
      (payload 31) (queryResult p hD H pub c1 payload) =
      (UnifiedRun.transcript p hD H pub c1 payload 32).rounds := by
  rw [UnifiedRun.transcript_succ]
  simp only [FS.Prefix.ext]
  rw [← UnifiedRecordCompletion.completed_eq_transcript p hD H pub c1 payload
    hl he 31 (by decide)]
  rw [query_challenge]
  simp [TranscriptView.withQuery, UnifiedRun.message, UnifiedSampler.liftQuery]

#print axioms query_challenge
#print axioms query_state
#print axioms rho_address
#print axioms rho_challenge
#print axioms prefix32

end AspisR1.UnifiedQueryRun
end
