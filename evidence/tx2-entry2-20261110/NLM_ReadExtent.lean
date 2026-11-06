import NLM_ActualRead
import NLE_CallerScope
set_option autoImplicit false
noncomputable section
namespace NLM_ReadExtent
open Aeneas Aeneas.Std Result AspisR1 AspisR1.S2W_D189Entry
/-- Derive native-call scope clauses from the actual CLOSED getter calls.
These are entered-call conditions, not independently supplied length facts. -/
theorem scope (ops : AdapterRw.Ops) (e : Entry)
 (account proof checkpoint : Slice U8) (publicBytes : Array U8 1880#usize)
 (end_ : Usize) (publicAddress proofAddress checkpointAddress : Nat)
 (readProof : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops)
   (e.snapshot 0 58295 58295)=.ok (.Ok account))
 (readCheckpoint : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (NGL_CloneDomain.install ops)
   (e.snapshot 6 1768 1768)=.ok (.Ok checkpoint))
 (checkedLength : account.val.length=end_.val)
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   account {start:=688#usize,«end»:=end_}=.ok proof) :
 NLE_SafeCuts.Scope (NLE_CallerScope.metadata publicAddress proofAddress checkpointAddress
   publicBytes.to_slice proof checkpoint) :=
 NLE_CallerScope.scope e account proof checkpoint publicBytes end_ publicAddress proofAddress
  checkpointAddress (NLM_ActualRead.snapshot_bytes ops e 0 58295 58295 account readProof)
  (NLM_ActualRead.snapshot_bytes ops e 6 1768 1768 checkpoint readCheckpoint) checkedLength range
#print scope
#print axioms scope
end NLM_ReadExtent
