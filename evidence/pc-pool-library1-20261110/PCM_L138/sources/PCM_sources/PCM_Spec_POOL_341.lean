import PCM_Witness
import PCM_StepLaws
import PCM_Carriers
import PCM_ErrorMap
set_option autoImplicit false
namespace PCM_POOL_341
open RSL PCM PCM.Computation
abbrev Args := B32 × AccountInfo × AccountInfo × AccountInfo × Master × Checkpoint × LaneState × Request
structure Children where
  outputLane : Child Digest UInt8
  laneMatches : Child (B32 × B32 × UInt8 × UInt8 × B32) Bool

def Ref (C : Children) (a : Args) : Computation Unit := do
  let (program,ma,ca,la,master,checkpoint,lane,request) := a
  check (request.pool_program != program) (.custom 0x4153202b)
  let (pool,deployment,sequence,root,asset,destination) := match request.pub with
    | .transfer p => (p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.asset_id,zero32)
    | .withdrawal p => (p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.asset_id,p.destination_token_account)
  let output ← mapError (fun _ => .custom 0x41532007) (C.outputLane.call request.pub.nullifier)
  check (pool != ma.key || master.identity.pool != pool || deployment != master.identity.deployment_domain ||
    asset != master.identity.asset_id || ca.key == zero32 || checkpoint.master != pool ||
    checkpoint.deployment_domain != deployment || checkpoint.checkpoint_sequence != sequence ||
    checkpoint.global_root != root) (.custom 0x4153202b)
  let address ← C.laneMatches.call (program,ma.key,output,lane.bump,la.key)
  check (!address || lane.master != pool || lane.lane_id != output ||
    (master.initialized_lane_mask &&& (1 <<< output)) == 0 ||
    (request.pub.transitionKind == 2 && destination == zero32)) (.custom 0x4153202b)

def RowSpec (C : Children) (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

theorem rejects_wrong_error (C : Children) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  let a : Args := ⟨B32.ofFill 1,PCM.account0,PCM.account0,PCM.account0,⟨0,PCM.identity0,PCM.policy0,0,false,0,[]⟩,⟨0,zero32,zero32,0,[],[]⟩,PCM.lane0,PCM.request0⟩
  apply PCM.rejects_error (fun _ : Args => True) (Ref C) a (.custom 0x4153202b) .invalidArgument trivial
  · unfold Ref
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_341
