import SCH_CollisionKnownSuffix
set_option autoImplicit false
namespace AspisR1.SCH_EventKnownSuffix
open FS AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem same {A B : Type} (iv : State) (Q : Nat)
    (left : View Bytes State A) (right : View Bytes State B)
    (suffix : List (Bytes × State)) (logs : left.1 = right.1 ++ suffix)
    (known : ∀ a ∈ suffix.map Prod.fst, a ∈ right.1.map Prod.fst) :
    BinRawByteCollisionTargets.event iv Q left ↔ BinRawByteCollisionTargets.event iv Q right := by
  unfold BinRawByteCollisionTargets.event
  rw [logs]
  exact SCH_CollisionKnownSuffix.same _ _ _ _ known

#print axioms same
end AspisR1.SCH_EventKnownSuffix
