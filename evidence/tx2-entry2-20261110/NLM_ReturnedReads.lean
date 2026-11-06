import NLM_SnapshotReturned
import NLM_ActualRead
set_option autoImplicit false
noncomputable section
namespace NLM_ReturnedReads
open Aeneas Aeneas.Std AspisR1.S2W_D189Entry NLM_Snapshot
/-- Eliminate a local returned-snapshot cut, then use the actual owned getter
on that SAME returned value. Allocation success and byte extent are derived,
not supplied as root assumptions. -/
theorem data (ops : AdapterRw.Ops) (e : Entry) (t a lo hi : Nat)
 (owned : List NLM_Snapshot.Owned) (allocation : Result Unit)
 (value : NLM_Snapshot.Owned) (post : NLM_Snapshot.State) (bytes : Slice U8)
 (entered : (G (ready e t owned) a lo hi allocation).result=.ok (value,post))
 (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops)
   value=.ok (.Ok bytes)) :
 (e.snapshot a lo hi).bytes=.Ok bytes ∧ post=returned (ready e t owned) a lo hi := by
 obtain ⟨same,frame⟩ := returned_state e t a lo hi owned allocation value post entered
 subst value
 exact ⟨NLM_ActualRead.snapshot_bytes ops e a lo hi bytes read,frame⟩
#print data
#print axioms data
end NLM_ReturnedReads
