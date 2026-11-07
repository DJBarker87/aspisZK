import NMT_R2_CheckpointOwner
set_option autoImplicit false
noncomputable section
namespace NMT_R2_CheckpointEquation
open Aeneas Aeneas.Std NMT_345 NMT_R2_EmittedLength
attribute [local instance] Classical.propDecidable
/-- One actual CLOSED341 call, whose std clone now has its allocation arm. -/
def native (keep : Bool) (a : Account) (program : Key) (writable : Bool) :=
 AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint (ops keep) (toAccount a) program writable

def finish (r : core.result.Result Usize OldPE) : Result (core.result.Result Unit OldPE) :=
 match r with
 | .Err e => .ok (.Err e)
 | .Ok n => if n != 1768#usize then .ok (.Err .InvalidAccountData) else .ok (.Ok ())

/-- The length clone is reached only after the four original metadata guards. -/
theorem equation (keep : Bool) (a : Account) (program : Key) (writable : Bool) :
 native keep a program writable =
 (if a.owner ≠ program then .ok (.Err .InvalidAccountData)
 else if a.is_signer then .ok (.Err .InvalidAccountData)
 else if a.executable then .ok (.Err .InvalidAccountData)
 else if a.is_writable != writable then .ok (.Err .InvalidAccountData)
 else do
  let length ← AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len (ops keep) (toAccount a)
  finish length) := by
 have comparison := NMT_R2_CheckpointOwner.owner_check keep a program
 unfold NMT_R2_CheckpointOwner.ownerCheck at comparison
 simp only [AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner,toAccount,bind_tc_ok] at comparison
 unfold native AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
 simp only [AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner,bind_tc_ok]
 rw [show (toAccount a).owner = a.owner from rfl,comparison]
 simp only [bind_tc_ok]
 by_cases h : a.owner ≠ program
 · simp [h]
 · simp only [h,decide_false,if_false]
   change (if a.is_signer then _ else if a.executable then _ else if a.is_writable != writable then _ else _) = _
   split
   · rfl
   · split
     · rfl
     · split
       · rfl
       · cases hr : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len (ops keep) (toAccount a) with
         | fail e => rfl
         | div => rfl
         | ok value =>
          cases value with
          | Err e => rfl
          | Ok n =>
           simp only [ops,NGL_CheckpointModel.install]
           rfl
#print axioms equation
end NMT_R2_CheckpointEquation
end
