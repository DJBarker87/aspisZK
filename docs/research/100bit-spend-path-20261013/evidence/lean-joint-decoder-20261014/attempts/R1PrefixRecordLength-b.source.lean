import R1PrefixRecordFacts
import R1PrefixAnswers

/-! Length accounting for the joint semantic/opening prefix and its answers. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.PrefixRecordLength

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem ordinary_length (ss sb : Nat → State) (sm : Nat → M) (n : Nat)
    (os ob : Nat → State) (om : Nat → M) (k : Nat) :
    (PrefixRecordFacts.ordinary ss sb sm n os ob om k).length = n + 1 + k := by
  unfold PrefixRecordFacts.ordinary
  rw [List.length_append, List.length_append, List.length_singleton,
    RawRoundCompletion.recs_length, RawRoundCompletion.recs_length]

theorem completeRounds_length (p : Params M Cv L)
    (T : Table (Addr L) State) (acc : Addr L → State)
    (offset : Nat) (rs : List (Rec M)) :
    (completeRounds p T acc offset rs).length = rs.length := by
  exact FS2.Duplex.completeRounds_length p T acc offset rs

theorem fromAnswers_length (p : Params M Cv L)
    (T : Table (Addr L) State) (offset : Nat)
    (rs : List (Rec M)) (as : List State) :
    (PrefixAnswers.fromAnswers p T offset rs as).length = rs.length := by
  unfold PrefixAnswers.fromAnswers
  exact completeRounds_length p T
    (R0C.V3.DQ.accFrom (PrefixAnswers.missing p T rs) as) offset rs

#print axioms ordinary_length
#print axioms completeRounds_length
#print axioms fromAnswers_length

end AspisR1.PrefixRecordLength
end
