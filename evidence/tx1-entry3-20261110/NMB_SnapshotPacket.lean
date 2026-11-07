import NMB_Heap
import NIM_NHY_SnapshotJoin
set_option autoImplicit false
noncomputable section
namespace NMB_SnapshotPacket
open Aeneas Aeneas.Std Result AspisR1 S2Trust
/-- Algebraic view used ONLY to specialize CLOSED343's value theorem. No
runtime library is ever asserted related to this view's ambient heap. -/
def entryAt (x : NMB_Input.Input) (a : Nat) : S2W_D189Entry.Entry :=
 ⟨x.handles,fun _=>⟨x.descriptors a,0,x.rentEpoch a⟩,x.buffers,x.base,x.provenance⟩
/-- Reuse the CLOSED snapshot reference packet at its OWN domain. The metadata
arguments are the SAME occurrence's original descriptor. This is a value
specialization, not a second existential execution or world switch. -/
theorem value (x : NMB_Input.Input) (a : Nat) (l1 l2 : Usize) :
 let d := x.descriptors a
 (do let returned ← NHJ_SnapshotReference.snapshot_ref d.key d.owner
       d.is_signer d.is_writable d.executable l1 l2
       (.Ok (x.buffers (x.handles a).1))
     ok (NHJ_SnapshotAssociation.port returned)) =
 ok (x.snapshot a l1.val l2.val) :=
 NHJ_SnapshotPacket.cohort_return (entryAt x a) a l1 l2
/-- Original SDK world, original heap, generic ambient carrier: the shared
bracket derives success from zero counters and valid admission. -/
theorem bracket {W : Type} (x : NMB_Input.Input)
 (L : Library W (Nat → NMB_Input.Owned)) (sdk : S2TrustedSdkBorrow L)
 (w : W) (related : L.related w (NMB_Heap.heap x)) (valid : Valid (NMB_Heap.heap x)) (a : Nat) :
 ∃ token owner w1 w2 w3,
 L.run w (.shared a token owner)=(w1,.guard token) ∧
 L.run w1 (.deref token)=(w2,.payload ((NMB_Heap.heap x).payload ((NMB_Heap.heap x).accounts a).1)) ∧
 L.run w2 (.drop token)=(w3,.unit) ∧ L.related w3 (NMB_Heap.heap x) := by
 obtain ⟨token,owner,enabled⟩ := NHJ_SdkDomains.enabled_exists (NMB_Heap.heap x) a rfl
 obtain ⟨w1,w2,w3,h1,h2,h3,h4⟩ := NHJ_SdkBorrowPacket.returning_shared
  L sdk w (NMB_Heap.heap x) related valid a token owner enabled
  (by change (0 : Int)≤0; omega)
  (by change (0 : Int)<maxCounter; unfold maxCounter; omega)
 exact ⟨token,owner,w1,w2,w3,h1,h2,h3,h4⟩
#print value
#print bracket
#print axioms value
#print axioms bracket
end NMB_SnapshotPacket
