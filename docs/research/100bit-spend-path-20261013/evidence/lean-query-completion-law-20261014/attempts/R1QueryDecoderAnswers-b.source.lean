import R1QueryCompletionSupport
import R0C.V3.DQDecodes

/-! List-answer adapters for the query-round recovery component. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryDecoder

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

def fromAnswers (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (as : List State) :=
  recover p T (R0C.V3.DQ.accFrom (missing p T endpoint) as) endpoint

theorem fromAnswers_map (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (H : Addr L → State) :
    fromAnswers p T endpoint ((missing p T endpoint).map H) = recover p T H endpoint := by
  unfold fromAnswers
  apply recover_congr_on_missing
  intro b hb
  exact R0C.V3.DQ.accFrom_map H (missing p T endpoint) b hb

theorem fromAnswers_take_append (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (as bs : List State)
    (hlen : as.length = (missing p T endpoint).length) :
    fromAnswers p T endpoint ((as ++ bs).take (missing p T endpoint).length) =
      fromAnswers p T endpoint as := by
  unfold fromAnswers
  apply recover_congr_on_missing
  intro b hb
  congr 1
  rw [List.take_append_of_le_length (by omega),
    List.take_of_length_le (by omega)]

#print axioms fromAnswers_map
#print axioms fromAnswers_take_append

end AspisR1.QueryDecoder
end
