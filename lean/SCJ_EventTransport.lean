import SCJ_AlignedEvent
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_Projection
open FS AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
/-- A VALID implication with its necessary causal interface exposed.
The actual SCE/F3X recorder instance of alignment remains unproved; ordinary
sublist inclusion alone is refuted by event_implies_refuted. -/
theorem event_implies_aligned {X Y : Type} (iv : State) (Q : Nat)
    (small : View Bytes State X) (full : View Bytes State Y)
    (alignment : SCJ_Alignment.Aligned Q emptyTable emptyTable small.1 full.1) :
    BinRawByteCollisionTargets.event iv Q small →
      BinRawByteCollisionTargets.event iv Q full :=
  SCJ_AlignedEvent.hits iv BinRawByteCollisionTargets.pred Q alignment

theorem not_all_sublists_aligned (Q : Nat) :
    ∃ small full : List (Bytes × State), small.Sublist full ∧
      ¬ SCJ_Alignment.Aligned (Q+2965) emptyTable emptyTable small full := by
  obtain ⟨small,full,sub,clean,hit⟩ := clean_transport_refuted Q
  exact ⟨small,full,sub,fun aligned => clean
    (event_implies_aligned SelectedTranscriptParams.params.iv (Q+2965) (small,()) (full,()) aligned hit)⟩

#print axioms event_implies_aligned
#print axioms not_all_sublists_aligned
end AspisR1.SCJ_Projection
end
