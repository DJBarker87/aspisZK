import SCJ_BeforeTable
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCJ_Projection
open FS FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Sufficient event IMPLICATION, at the same full-log charged budget.
It needs preservation of FIRST-occurrence order on the actual recorders.
SCF_Charge supplies the full budget; a sublist alone does not supply order. -/
theorem event_implies {X Y : Type} (iv : State) (Q : Nat) (H : Bytes → State)
    (small : View Bytes State X) (full : View Bytes State Y)
    (smallCons : ∀ q ∈ small.1, q.2 = H q.1)
    (fullCons : ∀ q ∈ full.1, q.2 = H q.1)
    (reads : ∀ a, Read small.1 a → Read full.1 a)
    (order : ∀ b a, Read small.1 a → Before small.1 b a → Before full.1 b a)
    (budget : firstReads emptyTable full.1 ≤ Q) :
    BinRawByteCollisionTargets.event iv Q small →
      BinRawByteCollisionTargets.event iv Q full := by
  intro hit
  obtain ⟨a,read,_,badAt⟩ := SCJ_FirstHitWitness.witness
    (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) H small.1
    emptyTable smallCons hit
  have fullRead := reads a read
  have smallFull := SCJ_BeforeTable.extension H small.1 full.1 smallCons fullCons order a read
  have fullBudget := AllAddressCollisionTrace.small_before_read H full.1 a
    fullCons fullRead Q budget
  have fullBad := SCJ_TableExtension.bad iv BinRawByteCollisionTargets.pred Q a (H a)
    _ _ smallFull fullBudget badAt
  exact FS.hitsBad_of_first _ H a full.1 emptyTable fullCons fullRead rfl fullBad

#print axioms event_implies
end AspisR1.SCJ_Projection
end
