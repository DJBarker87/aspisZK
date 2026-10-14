import R1QueryDecoderAnswers

/-! The oracle-answer list instance of the query-round recovery wrapper. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryDecoder

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem fromAnswers_correct (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s : Nat → State)
    (hstep : ∀ j < 8, s (j + 1) = H (advanceA p (s j)))
    (hread : ∀ j < 8, Read tr (advanceA p (s j)))
    (a c : Addr L) (haread : Read tr a) (hcread : Read tr c)
    (hparse : (parseAbsorb a).isSome) (hroot : s 0 = H a)
    (hprefix : c.toBytes.take 32 = bytes (QueryFirstRead.result p H s).2) :
    fromAnswers p (tableBefore emptyTable tr c) (QueryFirstRead.result p H s).2
      ((missing p (tableBefore emptyTable tr c) (QueryFirstRead.result p H s).2).map H) =
      some (a, QueryFirstRead.result p H s) := by
  rw [fromAnswers_map]
  exact recover_correct_on_missing p H tr Qtot hcons hQ hcoll s hstep hread
    a c haread hcread hparse hroot hprefix H (fun _ _ => rfl)

#print axioms fromAnswers_correct

end AspisR1.QueryDecoder
end
