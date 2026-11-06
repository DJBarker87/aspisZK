import NIM_NHJ_SnapshotPacket
import NLM_SnapshotReturned
set_option autoImplicit false
noncomputable section
namespace NLM_SnapshotCallee
open Aeneas Aeneas.Std AspisR1.S2W_D189Entry
/-- CLOSED TX2:239's exact value reference at the caller's SAME snapshot.
This cites its canonical owner module; it is not a new snapshot row proof. -/
def reference (e : Entry) (a : Nat) (lo hi : Usize) :=
 let old := (e.records (e.handles a).1).owned
 do let value ← NHJ_SnapshotReference.snapshot_ref old.key old.owner
     old.is_signer old.is_writable old.executable lo hi (.Ok (e.buffers (e.handles a).1))
    Result.ok (NHJ_SnapshotAssociation.port value)

theorem source (e : Entry) (a : Nat) (lo hi : Usize) :
 reference e a lo hi=.ok (e.snapshot a lo.val hi.val) :=
 NHJ_SnapshotPacket.cohort_return e a lo hi
/-- A returned local occurrence supplies the exact CLOSED callee value.
No allocation-success or caller-selected SDK byte reply is added. Physical
native parent/call-site installation remains separate. -/
theorem returned (e : Entry) (t a : Nat) (lo hi : Usize)
 (owned : List NLM_Snapshot.Owned) (allocation : Result Unit)
 (value : NLM_Snapshot.Owned) (post : NLM_Snapshot.State)
 (entered : (NLM_Snapshot.G (NLM_Snapshot.ready e t owned) a lo.val hi.val allocation).result=.ok (value,post)) :
 reference e a lo hi=.ok value := by
 obtain ⟨same,_⟩ := NLM_Snapshot.returned_state e t a lo.val hi.val owned allocation value post entered
 subst value
 exact source e a lo hi
#print source
#print returned
#print axioms source
#print axioms returned
end NLM_SnapshotCallee
