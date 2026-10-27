import R1AppendNode
import R1PairCopyLinks
import R0P.Occupancy
import AspisFormal.Pool.V7PairLeafOccupancy

/-! The append leaf is the ordered output pair, with the existing algebraic
occupancy relation. Transfers append recipient/change; withdrawals append
change/zero. This derives the pair from gates and public digest bindings. -/
set_option autoImplicit false
namespace AspisR1.AppendPair
open R0P AspisPool.V7PairLeafOccupancy
variable {K : Type} [Field K]

def leaf (A : Trace K) : PairLeaf K where
  firstCommitment := AppendNode.left A 33
  secondOccupied := A 0 1018
  secondCommitment := fun i => A ⟨2 + i.val, by omega⟩ 1018
  secondOccupancyInverse := A 1 1018

theorem leaf_valid (pub : Public K) (A : Trace K)
    (ho : Holds occupancyFamily pub A) : (leaf A).Valid := by
  have h := (occupancy_holds_iff pub A).mp ho |>.1 1018 (Or.inr rfl)
  exact ⟨h.1, sub_eq_zero.mp h.2.1, h.2.2.1, h.2.2.2⟩

theorem pair_output (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) :
    OutputNotes.output A 33 = nodeCompress (leaf A).firstCommitment (leaf A).secondCommitment := by
  rw [AppendNode.node_step pub A hs hpo 33 (by right; constructor <;> decide)]
  have hr : AppendNode.right A 33 = (leaf A).secondCommitment := by
    funext i
    exact (PairCopyLinks.right_cells pub A hb i).symm
  rw [hr]
  rfl

theorem transfer_first (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) (hd : Holds digestFamily pub A)
    (hv : pub.variant = .privateTransfer) (recipient : R0P.Digest K)
    (hpresent : pub.recipient = some recipient) : (leaf A).firstCommitment = recipient := by
  funext i
  exact (PairCopyLinks.first_transfer pub A hb hv i).symm.trans
    ((digest_holds_iff pub A).mp hd |>.2.2.1 recipient hpresent i)

theorem transfer_second (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) (hd : Holds digestFamily pub A)
    (hv : pub.variant = .privateTransfer) : (leaf A).secondCommitment = pub.change := by
  funext i
  exact (PairCopyLinks.second_transfer pub A hb hv i).symm.trans
    ((digest_holds_iff pub A).mp hd |>.2.2.2.1 i)

theorem withdrawal_first (pub : Public K) (A : Trace K)
    (hb : CopyLinkBalance pub A) (hd : Holds digestFamily pub A)
    (hv : pub.variant = .withdrawal) : (leaf A).firstCommitment = pub.change := by
  funext i
  exact (PairCopyLinks.first_withdrawal pub A hb hv i).symm.trans
    ((digest_holds_iff pub A).mp hd |>.2.2.2.1 i)

theorem withdrawal_second (pub : Public K) (A : Trace K)
    (ho : Holds occupancyFamily pub A) (hv : pub.variant = .withdrawal) :
    (leaf A).secondCommitment = fun _ => 0 := by
  apply valid_empty_second_commitment_zero (leaf A) (leaf_valid pub A ho)
  have h := (occupancy_holds_iff pub A).mp ho |>.2.2
  simpa only [leaf, hv] using h

theorem transfer_output (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) (hd : Holds digestFamily pub A)
    (hv : pub.variant = .privateTransfer) (recipient : R0P.Digest K)
    (hpresent : pub.recipient = some recipient) :
    OutputNotes.output A 33 = nodeCompress recipient pub.change := by
  rw [pair_output pub A hs hpo hb, transfer_first pub A hb hd hv recipient hpresent,
    transfer_second pub A hb hd hv]

theorem withdrawal_output (pub : Public K) (A : Trace K)
    (hs : Holds scheduleFamily pub A) (hpo : Holds poseidonScalarFamily pub A)
    (hb : CopyLinkBalance pub A) (hd : Holds digestFamily pub A)
    (ho : Holds occupancyFamily pub A) (hv : pub.variant = .withdrawal) :
    OutputNotes.output A 33 = nodeCompress pub.change (fun _ => 0) := by
  rw [pair_output pub A hs hpo hb, withdrawal_first pub A hb hd hv,
    withdrawal_second pub A ho hv]

#print axioms leaf_valid
#print axioms transfer_output
#print axioms withdrawal_output
end AspisR1.AppendPair
