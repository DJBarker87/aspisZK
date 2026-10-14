import R1UnifiedSemanticDecoder
import R1UnifiedRecordCompletion
import R1UnifiedSteps

/-! The deterministic semantic prefix and next ordinary opening challenge
have the typed decoder representation for rows 27 through 30. This is only
representation equality. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedOpeningView

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
    (k : Nat) (hk : k < 4) :
    UnifiedSemanticDecoder.view pub
      ⟨c1, UnifiedRecords.records p hD H pub c1 payload (27 + k), payload (27 + k)⟩
      (completeRounds p emptyTable H 0
          (UnifiedRecords.records p hD H pub c1 payload (27 + k)),
        (p.σ (27 + k)
            (H (squeezeA p (H (UnifiedSteps.address p hD H pub c1 payload (27 + k))))),
          H (advanceA p (H (UnifiedSteps.address p hD H pub c1 payload (27 + k)))))) =
      (UnifiedRun.transcript p hD H pub c1 payload (27 + k),
        UnifiedRun.message c1 payload (27 + k),
        UnifiedRun.challenge p hD H pub c1 payload (27 + k)) := by
  let n := 27 + k
  have hn31 : n ≤ 31 := by dsimp [n]; omega
  have hprefix : TranscriptView.ordinary c1
      (completeRounds p emptyTable H 0 (UnifiedRecords.records p hD H pub c1 payload n)) =
      (UnifiedRun.transcript p hD H pub c1 payload n).rounds :=
    UnifiedRecordCompletion.completed_eq_transcript p hD H pub c1 payload hl he n hn31
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
    (by dsimp [n]; omega)
  have hstep := UnifiedSteps.state_step p hD H pub c1 payload hl he n
    (by dsimp [n]; omega) (by dsimp [n]; omega)
  have hchallenge :
      UnifiedRun.challenge p hD H pub c1 payload n =
        liftChallenge
          (p.σ n (H (squeezeA p (H (UnifiedSteps.address p hD H pub c1 payload n)))),
            H (advanceA p (H (UnifiedSteps.address p hD H pub c1 payload n)))) := by
    change UnifiedRun.challenge p hD H pub c1 payload n = _
    rw [hchallenge0, hstep]
    rw [show UnifiedRecords.absorbed p hD H pub c1 payload n =
      H (UnifiedSteps.address p hD H pub c1 payload n) by rfl]
  change (⟨pub, TranscriptView.ordinary c1
        (completeRounds p emptyTable H 0 (UnifiedRecords.records p hD H pub c1 payload n))⟩,
      Message.payload (payload n),
      liftChallenge
        (p.σ n (H (squeezeA p (H (UnifiedSteps.address p hD H pub c1 payload n)))),
          H (advanceA p (H (UnifiedSteps.address p hD H pub c1 payload n))))) =
    (UnifiedRun.transcript p hD H pub c1 payload n,
      UnifiedRun.message c1 payload n, UnifiedRun.challenge p hD H pub c1 payload n)
  rw [hrounds]
  rw [show UnifiedRun.message c1 payload n = Message.payload (payload n) by
    cases h : n with
    | zero => dsimp [n] at h; omega
    | succ j => rfl]
  rw [← hchallenge]

#print axioms actual_output

end AspisR1.UnifiedOpeningView
end
