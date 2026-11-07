import PCM_Witness
import PCM_StepLaws
import PCM_Carriers
import PCM_ErrorMap
set_option autoImplicit false
namespace PCM_POOL_321
open RSL PCM PCM.Computation
abbrev Args := B32 × AccountInfo × List AccountInfo × AccountInfo
structure Children where
  aliasFree : Child (AccountInfo × List AccountInfo × AccountInfo) Unit
  master : Child (B32 × AccountInfo) Master
  lanes : Child (B32 × B32 × List AccountInfo) (List LaneState)
  globalRoot : Child (List Digest) Digest
  checkpointAddress : Child (B32 × B32 × UInt64) (B32 × UInt8)
  purePlan : Child (Master × List LaneState × Digest × UInt8) (Master × Checkpoint)
  freshPda : Child (AccountInfo × B32 × B32 × Nat) Preparation
  encodeMaster : Child Master Bytes
  encodeCheckpoint : Child Checkpoint Bytes

def Ref (C : Children) (a : Args) : Computation PlannedCheckpoint := do
  let (program,ma,lanes,ca) := a
  check (lanes.length != 8) (if lanes.length < 8 then .notEnoughAccountKeys else .invalidArgument)
  C.aliasFree.call (ma,lanes,ca)
  let master ← C.master.call (program,ma)
  let states ← C.lanes.call (program,ma.key,lanes)
  let root ← C.globalRoot.call (states.map (fun lane => lane.tree.root))
  let (expected,bump) ← C.checkpointAddress.call (program,ma.key,master.next_checkpoint_sequence)
  let (nextMaster,checkpoint) ← mapError (fun _ => .custom 0x41532003) (C.purePlan.call (master,states,root,bump))
  let _ ← C.freshPda.call (ca,program,expected,CHECKPOINT_ACCOUNT_BYTES)
  let masterImage ← mapError (fun _ => .custom 0x41532003) (C.encodeMaster.call nextMaster)
  let checkpointImage ← mapError (fun _ => .custom 0x41532003) (C.encodeCheckpoint.call checkpoint)
  Computation.pure ⟨ma.key,expected,checkpoint.lane_sequences,checkpointImage,masterImage⟩

def RowSpec (C : Children) (impl : Args → State → Env → Observation PlannedCheckpoint) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

theorem rejects_wrong_error (C : Children) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  let a : Args := ⟨zero32,PCM.account0,[],PCM.account0⟩
  apply PCM.rejects_error (fun _ : Args => True) (Ref C) a (.notEnoughAccountKeys) .invalidArgument trivial
  · unfold Ref
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_321
