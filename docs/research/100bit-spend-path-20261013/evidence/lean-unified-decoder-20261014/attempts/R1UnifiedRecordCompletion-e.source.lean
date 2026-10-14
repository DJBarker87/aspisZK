import R1UnifiedRecords
import R1CompletedView

/-! The completed abstract records reproduce the ordinary transcript prefix
through the first 31 rounds, provided row zero is the fixed C1 record. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedRecordCompletion

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.TranscriptView

variable {M Cv : Type} {L : Nat}

theorem completed_eq_transcript (p : Params M Cv L) (hD : 5 ≤ p.D)
    (H : Addr L → State) (pub : UnifiedSampler.Public L) (c1 : State)
    (payload : Nat → M) (hl : p.lbl 0 = 160)
    (he : p.enc (payload 0) = PublicInitFrame.emptyRecord) :
    ∀ n, n ≤ 31 →
      TranscriptView.ordinary c1
        (completeRounds p emptyTable H 0
          (UnifiedRecords.records p hD H pub c1 payload n)) =
        (UnifiedRun.transcript p hD H pub c1 payload n).rounds := by
  intro n
  induction n with
  | zero =>
      intro _
      rfl
  | succ n ih =>
      intro hn
      cases n with
      | zero =>
          rw [UnifiedRecords.records_succ]
          simp only [UnifiedRecords.records, RawRoundCompletion.recs,
            List.range_zero, List.map_nil, List.nil_append]
          rw [CompletedView.singleton_record]
          simp [emptyTable]
          rw [← UnifiedRecords.ordinary_challenge p hD H pub c1 payload hl he 0 (by decide)]
          rw [UnifiedRun.transcript_succ]
          rfl
      | succ k =>
          have hbound : k + 1 ≤ 31 := by omega
          have hnonempty :
              UnifiedRecords.records p hD H pub c1 payload (k + 1) ≠ [] := by
            intro hnil
            have hlen := UnifiedRecords.records_length p hD H pub c1 payload (k + 1)
            rw [hnil] at hlen
            simp at hlen
          rw [UnifiedRecords.records_succ]
          rw [CompletedView.append_record p emptyTable H c1
            (UnifiedRecords.records p hD H pub c1 payload (k + 1))
            (UnifiedRecords.previous p hD H pub c1 payload (k + 1),
              UnifiedRecords.absorbed p hD H pub c1 payload (k + 1),
              payload (k + 1), UnifiedRun.state p hD H pub c1 payload (k + 2))
            hnonempty]
          rw [UnifiedRecords.records_length]
          rw [ih hbound]
          simp [emptyTable]
          rw [← UnifiedRecords.ordinary_challenge p hD H pub c1 payload hl he
            (k + 1) (by omega)]
          conv_rhs => rw [UnifiedRun.transcript_succ]
          simp only [FS.Prefix.ext, UnifiedRun.message]

#print axioms completed_eq_transcript

end AspisR1.UnifiedRecordCompletion
end
