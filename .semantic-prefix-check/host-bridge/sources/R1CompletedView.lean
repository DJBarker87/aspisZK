import R1TranscriptView
import R1RawRoundAppend

/-! Pure list bookkeeping for exposing completed raw records in the view. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.CompletedView

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisR1.TranscriptView

variable {M Cv : Type} {L : Nat}

theorem append_record (p : Params M Cv L) (T : Table (Addr L) State)
    (acc : Addr L → State) (c1 : State) (rs : List (Rec M)) (r : Rec M)
    (hrs : rs ≠ []) :
    TranscriptView.ordinary c1 (completeRounds p T acc 0 (rs ++ [r])) =
      TranscriptView.ordinary c1 (completeRounds p T acc 0 rs) ++
        [(.payload r.2.2.1,
          TranscriptView.liftChallenge
            (p.σ rs.length
              ((T (squeezeA p r.2.1)).getD (acc (squeezeA p r.2.1))),
              r.2.2.2))] := by
  rw [completeRounds_append]
  have hcompleted : completeRounds p T acc 0 rs ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    rw [completeRounds_length] at hlen
    cases rs with
    | nil => simp at hrs
    | cons q qs => simp at hlen
  rw [TranscriptView.ordinary_append c1 _ _ hcompleted]
  simp [TranscriptView.later]

theorem singleton_record (p : Params M Cv L) (T : Table (Addr L) State)
    (acc : Addr L → State) (c1 : State) (r : Rec M) :
    TranscriptView.ordinary c1 (completeRounds p T acc 0 [r]) =
      [(.initial c1,
        TranscriptView.liftChallenge
          (p.σ 0 ((T (squeezeA p r.2.1)).getD (acc (squeezeA p r.2.1))),
            r.2.2.2))] := rfl

theorem complete_nil (p : Params M Cv L) (T : Table (Addr L) State)
    (acc : Addr L → State) (c1 : State) :
    TranscriptView.ordinary c1 (completeRounds p T acc 0 []) = [] := rfl

#print axioms append_record
#print axioms singleton_record
#print axioms complete_nil

end AspisR1.CompletedView
end
