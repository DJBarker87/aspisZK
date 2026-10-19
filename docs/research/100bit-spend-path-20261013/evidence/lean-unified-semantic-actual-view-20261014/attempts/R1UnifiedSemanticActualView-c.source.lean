import R1UnifiedSemanticDecoder
import R1UnifiedRecordCompletion

/-! The deterministic semantic prefix and its next challenge are represented
by the typed semantic decoder view. This is representation equality only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedSemanticActualView

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView

variable {M Cv : Type} {L : Nat}

theorem actual_output (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M)
    (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord)
    (n : Nat) (hn : 0 < n) (hn26 : n < 26) :
    UnifiedSemanticDecoder.view pub
      ⟨c1, UnifiedRecords.records p hD H pub c1 payload n, payload n⟩
      (completeRounds p emptyTable H 0
          (UnifiedRecords.records p hD H pub c1 payload n),
        (p.σ n (H (squeezeA p (H (UnifiedSteps.address p hD H pub c1 payload n)))),
          H (advanceA p (H (UnifiedSteps.address p hD H pub c1 payload n))))) =
      (UnifiedRun.transcript p hD H pub c1 payload n,
        UnifiedRun.message c1 payload n,
        UnifiedRun.challenge p hD H pub c1 payload n) := by
  have hprefix : TranscriptView.ordinary c1
      (completeRounds p emptyTable H 0
        (UnifiedRecords.records p hD H pub c1 payload n)) =
      (UnifiedRun.transcript p hD H pub c1 payload n).rounds :=
    UnifiedRecordCompletion.completed_eq_transcript p hD H pub c1 payload hl he n (by omega)
  have hstatement := UnifiedRun.transcript_statement p hD H pub c1 payload n
  have hrounds :
      (⟨pub, TranscriptView.ordinary c1
        (completeRounds p emptyTable H 0
          (UnifiedRecords.records p hD H pub c1 payload n))⟩ : UnifiedSampler.Prefix M Cv L) =
      UnifiedRun.transcript p hD H pub c1 payload n := by
    cases hrun : UnifiedRun.transcript p hD H pub c1 payload n with
    | mk statement rounds =>
      simp only [hrun] at hstatement hprefix ⊢
      cases hstatement
      simp_all
  have hchallenge0 := UnifiedRecords.ordinary_challenge p hD H pub c1 payload hl he n
    (by omega)
  have hstep := UnifiedSteps.state_step p hD H pub c1 payload hl he n (by omega) (by omega)
  have hchallenge :
      UnifiedRun.challenge p hD H pub c1 payload n =
        liftChallenge
          (p.σ n (H (squeezeA p (H (UnifiedSteps.address p hD H pub c1 payload n)))),
            H (advanceA p (H (UnifiedSteps.address p hD H pub c1 payload n)))) := by
    change UnifiedRun.challenge p hD H pub c1 payload n = _
    rw [hchallenge0, hstep]
    change liftChallenge
      (p.σ n (H (squeezeA p (UnifiedRecords.absorbed p hD H pub c1 payload n))),
        H (advanceA p (UnifiedRecords.absorbed p hD H pub c1 payload n))) = _
    rw [show UnifiedRecords.absorbed p hD H pub c1 payload n =
      H (UnifiedSteps.address p hD H pub c1 payload n) by rfl]
  change (⟨pub, TranscriptView.ordinary c1
        (completeRounds p emptyTable H 0
          (UnifiedRecords.records p hD H pub c1 payload n))⟩,
      Message.payload (payload n),
      liftChallenge
        (p.σ n (H (squeezeA p (H (UnifiedSteps.address p hD H pub c1 payload n)))),
          H (advanceA p (H (UnifiedSteps.address p hD H pub c1 payload n))))) =
    (UnifiedRun.transcript p hD H pub c1 payload n,
      UnifiedRun.message c1 payload n, UnifiedRun.challenge p hD H pub c1 payload n)
  rw [hrounds]
  rw [show UnifiedRun.message c1 payload n = Message.payload (payload n) by
    cases n with
    | zero => omega
    | succ k => rfl]
  rw [← hchallenge]

#print axioms actual_output

end AspisR1.UnifiedSemanticActualView
end
