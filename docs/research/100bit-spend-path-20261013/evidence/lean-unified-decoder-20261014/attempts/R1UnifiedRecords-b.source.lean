import R1UnifiedRun
import R1RawRoundCompletion
import R1UnifiedPayloadValue

/-! Ordinary raw records extracted from the deterministic unified run.
The next-state field includes row 26's reseed. The row-zero byte premises
are explicit, and no source or shared-oracle security claim is made. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedRecords

open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open TranscriptView

variable {M Cv : Type} {L : Nat}
variable (p : Params M Cv L) (hD : 5 ≤ p.D) (H : Addr L → State)
  (pub : UnifiedSampler.Public L) (c1 : State) (payload : Nat → M)

def previous : Nat → State
  | 0 => H (PublicInitFrame.addr pub.pubBytes pub.initFits c1)
  | i + 1 => UnifiedRun.state p hD H pub c1 payload (i + 1)

def absorbed (i : Nat) : State :=
  H (absorbA p (previous p hD H pub c1 payload i)
    (p.lbl i) (p.enc (payload i)) (p.encLen (payload i)))

def records (n : Nat) : List (Rec M) :=
  RawRoundCompletion.recs (previous p hD H pub c1 payload)
    (absorbed p hD H pub c1 payload) payload
    (fun j => UnifiedRun.state p hD H pub c1 payload (j + 1)) n

theorem records_length (n : Nat) :
    (records p hD H pub c1 payload n).length = n :=
  RawRoundCompletion.recs_length _ _ _ _ n

theorem records_succ (n : Nat) :
    records p hD H pub c1 payload (n + 1) =
      records p hD H pub c1 payload n ++
        [(previous p hD H pub c1 payload n, absorbed p hD H pub c1 payload n,
          payload n, UnifiedRun.state p hD H pub c1 payload (n + 1))] :=
  RawRoundCompletion.recs_succ _ _ _ _ n

theorem ordinary_challenge (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (i : Nat) (hi31 : i ≠ 31) :
    UnifiedRun.challenge p hD H pub c1 payload i =
      liftChallenge
        (p.σ i (H (squeezeA p (absorbed p hD H pub c1 payload i))),
          UnifiedRun.state p hD H pub c1 payload (i + 1)) := by
  apply Prod.ext
  · cases i with
    | zero =>
        change (eval H (DuplexSamplers.initial p
          (PublicInitFrame.addr pub.pubBytes pub.initFits c1)
          (PublicInitFrame.row0 p hD) 0 liftChallenge).toProgram).2.1 = _
        rw [DuplexSamplers.initial_eval]
        dsimp only [liftChallenge]
        rw [RowZeroCodec.row0_absorb p hD (payload 0) hl he]
        rfl
    | succ j =>
        simpa only [UnifiedRun.challenge, UnifiedRun.message, absorbed, previous,
          UnifiedRun.state, UnifiedSampler.absorb, liftChallenge] using
          UnifiedPayloadValue.sampler_payload_value p hD H (j + 1) (by omega) hi31
            (UnifiedRun.transcript p hD H pub c1 payload (j + 1)) (payload (j + 1))
  · exact (UnifiedRun.state_succ p hD H pub c1 payload i).symm

#print axioms records_length
#print axioms records_succ
#print axioms ordinary_challenge

end AspisR1.UnifiedRecords
end
