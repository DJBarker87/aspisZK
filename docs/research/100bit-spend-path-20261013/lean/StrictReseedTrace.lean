import R1StrictReseedDecoder

/-! The strict domain/tag decoder recovers the actual reseed before the
next absorb, with the same charged collision complements as the old local bridge. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.StrictReseedTrace
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem recover_before_next (p : Params M Cv L) (tag : Byte) (hL : 62 ≤ L)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (htail : ¬ hitsBad (ParsedStateCollision.bad TrailingStateFrame.tailState Qtot)
      emptyTable tr)
    (a c : Addr L) (ha : Read tr a) (hc : Read tr c)
    (hr : Read tr (OpeningReseedFrame.addr tag hL (H a)))
    (hp : c.toBytes.take 32 = bytes (H (OpeningReseedFrame.addr tag hL (H a)))) :
    let r := OpeningReseedFrame.addr tag hL (H a)
    let T := tableBefore emptyTable tr c
    Before tr a r ∧ Before tr r c ∧ T a = some (H a) ∧
      StrictReseedDecoder.recover tag T (H r) = some (r, H a) := by
  obtain ⟨har, hrc, hacell, _⟩ := ReseedBoundary.recover_before_next
    p tag hL H tr Qtot hcons hQ hold htail a c ha hc hr hp
  refine ⟨har, hrc, hacell, ?_⟩
  apply StrictReseedDecoder.recover_of_cell p H tr Qtot hcons hQ hold
    (tableBefore emptyTable tr c) (DuplexPrefixTable.table_consistent H tr hcons c)
  rw [tableBefore_eq H tr emptyTable c _ hcons, if_pos hrc]

#print axioms recover_before_next
end AspisR1.StrictReseedTrace
end
