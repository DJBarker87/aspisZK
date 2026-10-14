import R1JointTranscriptView
import R1UnifiedQueryRun

/-! A successful joint decoder output agrees with the unified 33-row run's
transcript, final message, and rho challenge in the source-level model. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointActualView

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.TranscriptView

variable {M Cv : Type} {L : Nat}

theorem actual_output (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State)
    (payload : Nat → M) (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord) :
    JointTranscriptView.view pub
      (c1, payload 31, payload 32,
        ((completeRounds p emptyTable H 0
            (UnifiedRecords.records p hD H pub c1 payload 31),
          some (UnifiedQueryRun.queryAddress p hD H pub c1 payload,
            UnifiedQueryRun.queryResult p hD H pub c1 payload)),
          (p.σ 32 (H (squeezeA p
              (H (UnifiedQueryRun.rhoAddress p hD H pub c1 payload)))),
            H (advanceA p (H (UnifiedQueryRun.rhoAddress p hD H pub c1 payload)))))) =
      (UnifiedRun.transcript p hD H pub c1 payload 32,
        UnifiedRun.message c1 payload 32,
        UnifiedRun.challenge p hD H pub c1 payload 32) := by
  rw [JointTranscriptView.view_some]
  have hprefix :
      (⟨pub, TranscriptView.withQuery c1
        (completeRounds p emptyTable H 0
          (UnifiedRecords.records p hD H pub c1 payload 31))
        (payload 31) (UnifiedQueryRun.queryResult p hD H pub c1 payload)⟩ :
          UnifiedSampler.Prefix M Cv L) =
        UnifiedRun.transcript p hD H pub c1 payload 32 := by
    cases hrun : UnifiedRun.transcript p hD H pub c1 payload 32 with
    | mk statement rounds =>
        have hstatement := UnifiedRun.transcript_statement p hD H pub c1 payload 32
        rw [hrun] at hstatement
        have hrounds := UnifiedQueryRun.prefix32 p hD H pub c1 payload hl he
        rw [hrun] at hrounds
        subst statement
        exact congrArg
          (fun rs : List (Message M × Challenge Cv) =>
            (⟨pub, rs⟩ : UnifiedSampler.Prefix M Cv L)) hrounds
  rw [hprefix]
  have hmessage : UnifiedRun.message c1 payload 32 = .payload (payload 32) := rfl
  rw [← hmessage]
  rw [← UnifiedQueryRun.rho_challenge p hD H pub c1 payload]
  rfl

#print axioms actual_output

end AspisR1.JointActualView
end
