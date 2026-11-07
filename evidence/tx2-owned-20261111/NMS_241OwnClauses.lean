import NMS_EmittedLinks
import NMN_064
set_option autoImplicit false
noncomputable section
namespace NMS_241OwnClauses
open Aeneas Aeneas.Std AdapterRw
abbrev Accounts := Slice r1_pool_adapter.owned.OwnedAccount
/-- Predicate only on241's original account vector. The owned representation
permits length and bytes Results to disagree;241 does not recheck checkpoint
byte length, so this clause must be installed by caller240's snapshot. -/
def CheckpointBytes (accounts : Accounts) : Prop :=
 ∀ account bytes,
  Slice.index_usize accounts 6#usize = .ok account →
  account.bytes = .Ok bytes → bytes.deref.val.length = 1768
/-- Predicate only on the original account buffers and their deterministic
suffix projection. This is NMQ's admitted064 Root0 placement, passed upward to
240; no global/headline Root0 or injectivity claim is made. -/
def Root0Bytes (accounts : Accounts) : Prop :=
 ∀ proofAccount checkpointAccount proofBytes checkpointBytes suffix,
  Slice.index_usize accounts 0#usize = .ok proofAccount →
  Slice.index_usize accounts 6#usize = .ok checkpointAccount →
  proofAccount.bytes = .Ok proofBytes →
  checkpointAccount.bytes = .Ok checkpointBytes →
  core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   proofBytes.deref {start := 688#usize, «end» := Slice.len proofBytes.deref} = .ok suffix →
  NLP_InputDomain.Root0 checkpointBytes.deref suffix

def Domain (accounts : Accounts) : Prop := CheckpointBytes accounts ∧ Root0Bytes accounts
#print CheckpointBytes
#print Root0Bytes
end NMS_241OwnClauses
