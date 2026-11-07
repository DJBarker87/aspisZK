import PCM_Rejection
import PCM_Spec_POOL_308
import PCM_Algebra
import PCM_ErrorMap
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_327
open RSL PCM PCM.Computation
structure Args where
  program : B32
  accounts : List AccountInfo
  data : Bytes
  rent : PCM.Rent
structure Children where
  exactCount : Child (List AccountInfo × Nat) Unit
  uniqueAccounts : Child (List AccountInfo) Unit
  payerAndSystem : Child (AccountInfo × AccountInfo) Unit
  planCheckpoint : Child (B32 × AccountInfo × List AccountInfo × AccountInfo) PlannedCheckpoint
  freshPda : Child (AccountInfo × B32 × B32 × Nat) Preparation
  decodeCheckpoint : Child Bytes Checkpoint
  createPda : Child (AccountInfo × AccountInfo × AccountInfo × Nat × B32 × List Bytes) Unit
  programOwnedZeroed : Child (AccountInfo × B32 × Nat × PCM.Rent) Unit

def Ref (C : Children) (a : Args) : Computation Unit := do
  Computation.ofExcept (PCM_POOL_308.model a.data)
  C.exactCount.call (a.accounts,12)
  C.uniqueAccounts.call a.accounts
  let master ← index a.accounts 0
  let checkpoint ← index a.accounts 9
  let payer ← index a.accounts 10
  let system ← index a.accounts 11
  let lanes := (a.accounts.drop 1).take 8
  C.payerAndSystem.call (payer,system)
  let planned ← C.planCheckpoint.call (a.program,master,lanes,checkpoint)
  let prep ← C.freshPda.call (checkpoint,a.program,planned.checkpoint,CHECKPOINT_ACCOUNT_BYTES)
  if prep == .createOrAllocateSystemOwned then
    let state ← mapError (fun _ => .custom 0x41532003) (C.decodeCheckpoint.call planned.checkpoint_image)
    C.createPda.call (payer,checkpoint,system,CHECKPOINT_ACCOUNT_BYTES,a.program,
      [SEED_CHECKPOINT,master.key.bytes,u64le state.checkpoint_sequence,[state.bump]])
  C.programOwnedZeroed.call (checkpoint,a.program,CHECKPOINT_ACCOUNT_BYTES,a.rent)
  guardScope master .exclusive fun _ =>
    guardScope checkpoint .exclusive fun _ => do
      write checkpoint planned.checkpoint_image
      write master planned.next_master_image

def RowSpec (C : Children) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

/-- The empty wire input reaches the real decoder's first error before
account lookup, allocation, or a runtime call. -/
theorem rejects_wrong_error (C : Children) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  let a : Args := ⟨zero32,[],[],PCM.rent0⟩
  apply PCM.rejects_error (fun _ : Args => True) (Ref C) a .invalidInstructionData .invalidArgument trivial
  · unfold Ref
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h

#print axioms rejects_wrong_error
end PCM_POOL_327
