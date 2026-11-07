import PCM_Spec_POOL_334
import PCM_Algebra
import PCM_ErrorMap
import PCM_Spec_POOL_328
set_option autoImplicit false
namespace PCM_POOL_330
open RSL PCM PCM.Computation
abbrev Args := PCM_POOL_328.Args
structure Children where
  decodeRequest : Child Bytes Request
  decodeMaster : Child (B32 × AccountInfo) Master
  decodeCheckpoint : Child (B32 × B32 × AccountInfo) Checkpoint
  outputLane : Child Digest UInt8
  decodeLane : Child (B32 × B32 × UInt8 × AccountInfo) LaneState
  requestAccounts : Child (B32 × AccountInfo × AccountInfo × AccountInfo × Master × Checkpoint × LaneState × Request) Unit
  spendLayout : Child (B32 × List AccountInfo × LaneState × Bool × Hints) SpendLayout
  payerAndSystem : Child (AccountInfo × AccountInfo) Unit
  planMarker : Child (B32 × AccountInfo × Marker) PlannedMarker
  tokenProgram : Child AccountInfo Unit
  planWithdrawal : Child (B32 × B32 × PoolIdentity × List AccountInfo × B32 × UInt32 × Option (UInt8 × UInt8)) WithdrawalPlan
  createMarker : Child (B32 × AccountInfo × List Bytes × AccountInfo × AccountInfo × AccountInfo × PlannedMarker × PCM.Rent) ReadyMarker
  verify : Child (B32 × AccountInfo × AccountInfo × AccountInfo × VerifierPolicy × List AccountInfo × AccountInfo × AccountInfo × Option AccountInfo × Request × UInt64) AuthenticatedResult
  validateResult : Child (B32 × B32 × B32 × Master × Checkpoint × LaneState × UInt8 × Request × TerminalResult) Unit
  nextLaneImage : Child (LaneState × TerminalResult) Bytes
  resultBytes : Child TerminalResult Bytes
  withdrawalInfos : Child (List AccountInfo) (List AccountInfo)
  exactDelta : Child (List AccountInfo × WithdrawalPlan) Unit
  writeNewPage : Child (AccountInfo × B32 × UInt64 × UInt64 × List Digest) Unit
  appendRoots : Child (AccountInfo × Header × List Digest) Unit

/-- Deployed direct-result-audit is OFF; both validation and result encoding
are real calls, with their allocation-abort prefixes kept. -/
def Ref (C : Children) (runtime : Runtime) (a : Args) (currentSlot : UInt64) : Computation Unit := do
  let (requestBytes,hints) ← Computation.ofExcept (PCM_POOL_334.model a.data)
  let request ← C.decodeRequest.call requestBytes
  let masterAccount ← accountAt a.accounts 0
  let checkpointAccount ← accountAt a.accounts 1
  let laneAccount ← accountAt a.accounts 2
  let master ← C.decodeMaster.call (a.program,masterAccount)
  let checkpoint ← C.decodeCheckpoint.call (a.program,masterAccount.key,checkpointAccount)
  let outputLane ← mapError (fun _ => .custom 0x41532007) (C.outputLane.call request.pub.nullifier)
  let lane ← C.decodeLane.call (a.program,masterAccount.key,outputLane,laneAccount)
  C.requestAccounts.call (a.program,masterAccount,checkpointAccount,laneAccount,master,checkpoint,lane,request)
  let withdrawal := match request.pub with | .withdrawal _ => true | .transfer _ => false
  check (!withdrawal && (hints.vault_authority != 0 || hints.vault_token_account != 0)) .invalidInstructionData
  let layout ← C.spendLayout.call (a.program,a.accounts,lane,withdrawal,hints)
  let payer ← index a.accounts layout.payer_index
  let system ← index a.accounts layout.system_program_index
  C.payerAndSystem.call (payer,system)
  let marker ← index a.accounts layout.marker_index
  let markerPayload : Marker := ⟨request.pub.transitionKind,masterAccount.key,
    master.identity.deployment_domain,request.pub.nullifier,checkpoint.checkpoint_sequence,
    checkpoint.global_root,request.verifier_profile,request.verifier_release⟩
  let planned ← C.planMarker.call (a.program,marker,markerPayload)
  let withdrawalPlan ← match request.pub with
    | .transfer _ => Computation.pure none
    | .withdrawal p => do
      let tokens ← PCM_POOL_328.subAccounts a.accounts layout.token_start 5
      let tokenProgram ← index tokens 4
      C.tokenProgram.call tokenProgram
      let plan ← C.planWithdrawal.call (a.program,masterAccount.key,master.identity,tokens,
        p.destination_token_account,p.amount,some (hints.vault_authority,hints.vault_token_account))
      Computation.pure (some plan)
  let ready ← C.createMarker.call (a.program,masterAccount,
    [SEED_MASTER,master.identity.asset_mint.bytes,[master.bump]],marker,payer,system,planned,a.rent)
  let registry ← PCM_POOL_328.subAccounts a.accounts layout.registry_start 2
  let verifier ← index a.accounts layout.verifier_index
  let proof ← index a.accounts layout.proof_index
  let verifierCheckpoint ← match layout.verifier_checkpoint_index with
    | none => Computation.pure none
    | some i => do let ac ← index a.accounts i; Computation.pure (some ac)
  let authenticated ← C.verify.call (a.program,masterAccount,checkpointAccount,laneAccount,
    master.verifier_policy,registry,verifier,proof,verifierCheckpoint,request,currentSlot)
  let result := authenticated.value
  C.validateResult.call (masterAccount.key,checkpointAccount.key,laneAccount.key,master,checkpoint,lane,outputLane,request,result)
  let laneImage ← C.nextLaneImage.call (lane,result)
  let resultBytes ← C.resultBytes.call result
  let page ← match layout.page with
    | .genesis | .same _ => index a.accounts 3
    | .rollover i _ => index a.accounts i
  guardScope laneAccount .exclusive fun _ =>
    guardScope page .exclusive fun _ =>
      guardScope marker .exclusive fun _ => do
        match withdrawalPlan with
        | none => Computation.pure ()
        | some plan => do
          let tokens ← PCM_POOL_328.subAccounts a.accounts layout.token_start 5
          let infos ← C.withdrawalInfos.call tokens
          runtime.invoke ⟨plan.instruction,infos,
            [["aspis-pool-vault-authority-v1".toUTF8.toList,masterAccount.key.bytes,[plan.authority_bump]]]⟩
          C.exactDelta.call (tokens,plan)
        write laneAccount laneImage
        match layout.page with
        | .genesis => C.writeNewPage.call (page,laneAccount.key,0,0,[lane.tree.root,result.verified_afterstate.next_root])
        | .same header => C.appendRoots.call (page,header,[result.verified_afterstate.next_root])
        | .rollover _ number => C.writeNewPage.call (page,laneAccount.key,number,result.verified_afterstate.next_pair_index,[result.verified_afterstate.next_root])
        write marker ready.encoded_marker
        emit (.sdk (.returnData resultBytes))
        let s ← get
        put {s with returnData := some (a.program,resultBytes)}

def RowSpec (C : Children) (runtime : Runtime)
    (impl : Args → UInt64 → State → Env → Observation Unit) : Prop :=
  ∀ slot, PCM.RowSpec (fun _ => True) (fun a => Ref C runtime a slot) (fun a => impl a slot)
end PCM_POOL_330
