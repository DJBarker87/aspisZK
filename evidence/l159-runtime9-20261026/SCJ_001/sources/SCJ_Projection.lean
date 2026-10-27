import SCI_Projection
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_Projection
open FS AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open SCI_Projection.OrderWitness

/-- The proposed generic implication is false for the EXACT release event,
even with one oracle, sublist inclusion and the common charged budget. -/
theorem event_implies_refuted (Q : Nat) :
    ¬ (∀ (H : Bytes → State) (small full : List (Bytes × State)),
      (∀ q ∈ small, q.2 = H q.1) →
      (∀ q ∈ full, q.2 = H q.1) →
      small.Sublist full → firstReads emptyTable small ≤ Q+2965 →
      firstReads emptyTable full ≤ Q+2965 →
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965) (small,()) →
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965) (full,())) := by
  intro transport
  obtain ⟨H,smallCons,fullCons,sub,smallBound,fullBound,hit,clean⟩ :=
    deleting_uncached_charged Q
  exact clean (transport H _ _ smallCons fullCons sub
    (smallBound.trans (by omega)) (fullBound.trans (by omega)) hit)

/-- Contrapositive failure: full-log cleanliness does not ensure projected-log
cleanliness. This is the direction required before using F3X's clean branch. -/
theorem clean_transport_refuted (Q : Nat) :
    ∃ (small full : List (Bytes × State)), small.Sublist full ∧
      ¬ BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965) (full,()) ∧
      BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965) (small,()) := by
  obtain ⟨_,_,_,sub,_,_,hit,clean⟩ := deleting_uncached_charged Q
  exact ⟨_,_,sub,clean,hit⟩

#print axioms event_implies_refuted
#print axioms clean_transport_refuted
end AspisR1.SCJ_Projection
end
