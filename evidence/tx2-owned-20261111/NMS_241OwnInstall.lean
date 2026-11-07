import NMS_GetterSuccess
import NMS_241OwnClauses
set_option autoImplicit false
noncomputable section
namespace NMS_241OwnInstall
open Aeneas Aeneas.Std AdapterRw

theorem checkpoint (ops : Ops) (accounts : NMS_241OwnClauses.Accounts)
 (own : NMS_241OwnClauses.CheckpointBytes accounts)
 (account : r1_pool_adapter.owned.OwnedAccount) (bytes : Slice U8)
 (indexed : Slice.index_usize accounts 6#usize = .ok account)
 (read : NMS_Emitted.get ops account = .ok (.Ok bytes)) : bytes.val.length = 1768 := by
 obtain ⟨original,stored,same⟩ := NMS_GetterSuccess.stored ops account bytes read
 rw [same]
 exact own account original indexed stored

theorem root0 (ops : Ops) (accounts : NMS_241OwnClauses.Accounts)
 (own : NMS_241OwnClauses.Root0Bytes accounts)
 (proofAccount checkpointAccount : r1_pool_adapter.owned.OwnedAccount)
 (proof checkpoint suffix : Slice U8)
 (proofIndexed : Slice.index_usize accounts 0#usize = .ok proofAccount)
 (checkpointIndexed : Slice.index_usize accounts 6#usize = .ok checkpointAccount)
 (proofRead : NMS_Emitted.get ops proofAccount = .ok (.Ok proof))
 (checkpointRead : NMS_Emitted.get ops checkpointAccount = .ok (.Ok checkpoint))
 (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
  proof {start := 688#usize, «end» := Slice.len proof} = .ok suffix) :
 NLP_InputDomain.Root0 checkpoint suffix := by
 obtain ⟨proofOriginal,proofStored,proofSame⟩ := NMS_GetterSuccess.stored ops proofAccount proof proofRead
 obtain ⟨checkpointOriginal,checkpointStored,checkpointSame⟩ := NMS_GetterSuccess.stored ops checkpointAccount checkpoint checkpointRead
 rw [proofSame] at range
 rw [checkpointSame]
 exact own proofAccount checkpointAccount proofOriginal checkpointOriginal suffix
  proofIndexed checkpointIndexed proofStored checkpointStored range
#print axioms checkpoint
#print axioms root0
end NMS_241OwnInstall
