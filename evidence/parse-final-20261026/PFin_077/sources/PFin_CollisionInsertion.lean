import PFin_CollisionTransport
import PFin_TraceInsertion
set_option autoImplicit false
noncomputable section
namespace AspisR1.PFin_CollisionInsertion
open FS FS2 FS2.Duplex AspisV8PairedCommitment
variable {I A : Type} [DecidableEq I] [Fintype A] [Inhabited A]

theorem transport {B : Nat} (iv : A) (pred : Fin B → I → Option A) (H : I → A)
    (left middle right audit : List (I × A)) (q r : Nat)
    (oldCons : ∀ x∈left++right,x.2=H x.1)
    (largerCons : ∀ x∈left++middle++right++audit,x.2=H x.1)
    (disjoint : ∀ a,Read right a → ¬Read middle a)
    (budget : firstReads emptyTable (left++middle++right++audit)≤r)
    (hit : hitsBad (AllAddressCollision.bad iv pred q) emptyTable (left++right)) :
    hitsBad (AllAddressCollision.bad iv pred r) emptyTable (left++middle++right++audit) := by
  apply PFin_CollisionTransport.ordered iv pred H _ _ q r oldCons largerCons ?_ ?_ budget hit
  · intro a read
    exact (PFin_TraceIndex.read_append _ _ _).mpr
      (Or.inl (PFin_TraceInsertion.read left middle right a read))
  · intro a b order readB
    have readA := order.1
    exact PFin_TraceIndex.before_append _ audit a b
      (PFin_TraceInsertion.read left middle right a readA)
      (PFin_TraceInsertion.read left middle right b readB)
      (PFin_TraceInsertion.before left middle right disjoint a b readA readB order)

#print axioms transport
end AspisR1.PFin_CollisionInsertion
end
