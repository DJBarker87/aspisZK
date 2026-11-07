import NIM_NHY_SnapshotJoin
set_option autoImplicit false
noncomputable section
namespace NLQ_ClosedSnapshotStep
open Aeneas Aeneas.Std Result AspisR1.S2W_D189Entry AspisR1.S2Trust
/-- Exact normal-return packet of CLOSED TX1:343. Both guard operations and
owned carrier are retained; allocator aborts are handled separately. -/
def Step {W : Type} (e : Entry) (L : Library W (Nat → Record))
 (before after : W) (a : Nat) (l1 l2 : Usize) : Prop :=
 ∃ token owner w1 w2,
  L.run before (.shared a token owner)=(w1,.guard token) ∧
  L.run w1 (.deref token)=(w2,.payload (e.heap.payload (e.heap.accounts a).1)) ∧
  L.run w2 (.drop token)=(after,.unit) ∧ L.related after e.heap ∧
  (let old := (e.records (e.handles a).1).owned
   (do
    let returned ← NHJ_SnapshotReference.snapshot_ref old.key old.owner
      old.is_signer old.is_writable old.executable l1 l2 (.Ok (e.buffers (e.handles a).1))
    ok (NHJ_SnapshotAssociation.port returned))=ok (e.snapshot a l1.val l2.val))
theorem at_site {W : Type} (e : Entry) (L : Library W (Nat → Record))
 (sdk : S2TrustedSdkBorrow L) (before : W) (related : L.related before e.heap)
 (valid : Valid e.heap) (a : Nat) (l1 l2 : Usize) :
 ∃ after,Step e L before after a l1 l2 := by
 obtain ⟨token,owner,w1,w2,after,h1,h2,h3,h4,h5⟩ :=
  NHY_SnapshotJoin.source e L sdk before related valid a l1 l2
 exact ⟨after,token,owner,w1,w2,h1,h2,h3,h4,h5⟩
theorem related_after {W : Type} (e : Entry) (L : Library W (Nat → Record))
 (before after : W) (a : Nat) (l1 l2 : Usize) (step : Step e L before after a l1 l2) :
 L.related after e.heap := by
 obtain ⟨_,_,_,_,_,_,_,related,_⟩ := step
 exact related
#print Step
#print axioms at_site
#print axioms related_after
end NLQ_ClosedSnapshotStep
