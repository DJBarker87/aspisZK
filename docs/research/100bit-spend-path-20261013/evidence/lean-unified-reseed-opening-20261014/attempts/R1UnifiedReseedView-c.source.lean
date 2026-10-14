import R1UnifiedSemanticDecoder
import R1UnifiedRecordCompletion
import R1UnifiedFramework
import R1UnifiedSteps

/-! The deterministic prefix through row 26 and the reseed challenge have the
semantic decoder representation. This is representation equality only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedReseedView

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView

variable {M Cv W : Type} {L : Nat}

theorem actual_output (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M)
    (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord) :
    UnifiedSemanticDecoder.view pub
      ⟨c1, UnifiedRecords.records p hD H pub c1 payload 26, payload 26⟩
      (completeRounds p emptyTable H 0
          (UnifiedRecords.records p hD H pub c1 payload 26),
        (p.σ 26 (H (squeezeA p (H (UnifiedSteps.address p hD H pub c1 payload 26)))),
          H (UnifiedSteps.reseedAddress p hD H pub c1 payload))) =
      (UnifiedRun.transcript p hD H pub c1 payload 26,
        UnifiedRun.message c1 payload 26,
        UnifiedRun.challenge p hD H pub c1 payload 26) := by
  have hprefix : TranscriptView.ordinary c1
      (completeRounds p emptyTable H 0
        (UnifiedRecords.records p hD H pub c1 payload 26)) =
      (UnifiedRun.transcript p hD H pub c1 payload 26).rounds :=
    UnifiedRecordCompletion.completed_eq_transcript p hD H pub c1 payload hl he 26 (by omega)
  have hstatement := UnifiedRun.transcript_statement p hD H pub c1 payload 26
  have hrounds :
      (⟨pub, TranscriptView.ordinary c1
        (completeRounds p emptyTable H 0
          (UnifiedRecords.records p hD H pub c1 payload 26))⟩ : UnifiedSampler.Prefix M Cv L) =
      UnifiedRun.transcript p hD H pub c1 payload 26 := by
    cases hrun : UnifiedRun.transcript p hD H pub c1 payload 26 with
    | mk statement rounds =>
      simp only [hrun] at hstatement hprefix ⊢
      cases hstatement
      simp_all
  have hchallenge0 := UnifiedRecords.ordinary_challenge p hD H pub c1 payload hl he 26
    (by decide)
  have hstep := UnifiedSteps.reseed_step p hD H pub c1 payload
  have hchallenge :
      UnifiedRun.challenge p hD H pub c1 payload 26 =
        liftChallenge
          (p.σ 26 (H (squeezeA p (H (UnifiedSteps.address p hD H pub c1 payload 26)))),
            H (UnifiedSteps.reseedAddress p hD H pub c1 payload)) := by
    change UnifiedRun.challenge p hD H pub c1 payload 26 = _
    rw [hchallenge0, hstep]
    rw [show UnifiedRecords.absorbed p hD H pub c1 payload 26 =
      H (UnifiedSteps.address p hD H pub c1 payload 26) by rfl]
  change (⟨pub, TranscriptView.ordinary c1
        (completeRounds p emptyTable H 0
          (UnifiedRecords.records p hD H pub c1 payload 26))⟩,
      Message.payload (payload 26),
      liftChallenge
        (p.σ 26 (H (squeezeA p (H (UnifiedSteps.address p hD H pub c1 payload 26)))),
          H (UnifiedSteps.reseedAddress p hD H pub c1 payload))) =
    (UnifiedRun.transcript p hD H pub c1 payload 26,
      UnifiedRun.message c1 payload 26, UnifiedRun.challenge p hD H pub c1 payload 26)
  rw [hrounds]
  rw [show UnifiedRun.message c1 payload 26 = Message.payload (payload 26) by rfl]
  rw [← hchallenge]

theorem firstCell_eq (p : Params M Cv L) (hD : 5 ≤ p.D)
    (extract : UnifiedSampler.Public L → Table (Addr L) State → Option W)
    (H : Addr L → State) (pub : UnifiedSampler.Public L)
    (c1 : State) (payload : Nat → M) :
    firstCell ((UnifiedProtocol.protocol p hD extract).chain H pub (c1, payload) 26) =
      some (UnifiedSteps.address p hD H pub c1 payload 26) := by
  rw [UnifiedProtocol.chain_eq p hD extract H pub (c1, payload) 26]
  change firstCell (UnifiedSampler.samp p hD 26
    (UnifiedRun.transcript p hD H pub c1 payload 26) (.payload (payload 26))) = _
  rw [UnifiedSampler.row_reseed]
  rw [UnifiedSteps.payload_address p hD H pub c1 payload 26 (by decide)]
  rfl

#print axioms actual_output
#print axioms firstCell_eq

end AspisR1.UnifiedReseedView
end
