import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_328
open RSL PCM PCM.Computation
structure Args where
  program : B32
  accounts : List AccountInfo
  data : Bytes
  rent : PCM.Rent
/-- Each slot names a real direct callee in frozen pair_forest.rs:988-1196.
No slot may be installed with a native Cut relation or a chosen success. -/
structure Children where
  decodeDeposit : Child Bytes DepositRequest
  decodeMaster : Child (B32 × AccountInfo) Master
  noteCommitment : Child (Digest × UInt32 × UInt32 × Digest) Digest
  depositLane : Child Digest UInt8
  decodeLane : Child (B32 × B32 × UInt8 × AccountInfo) LaneState
  singleOutput : Child Digest PairWitness
  leafDigest : Child PairWitness Digest
  prepareAppend : Child (LaneState × UInt8 × Digest) (Append × Bytes)
  rootLocation : UInt64 → Location
  zeroedPage : Child (AccountInfo × B32) Bool
  pageAddress : Child (B32 × B32 × UInt64) (B32 × UInt8)
  freshPda : Child (AccountInfo × B32 × B32 × Nat) Preparation
  currentPage : Child (B32 × AccountInfo × AccountInfo × LaneState × Bool × Option UInt8) Header
  exactCount : Child (List AccountInfo × Nat) Unit
  uniqueAccounts : Child (List AccountInfo) Unit
  tokenProgram : Child AccountInfo Unit
  planTransfer : Child (B32 × B32 × PoolIdentity × List AccountInfo × UInt32) TransferPlan
  transferInfos : Child (List AccountInfo) (List AccountInfo)
  payerAndSystem : Child (AccountInfo × AccountInfo) Unit
  createPda : Child (AccountInfo × AccountInfo × AccountInfo × Nat × B32 × List Bytes) Unit
  programOwnedZeroed : Child (AccountInfo × B32 × Nat × PCM.Rent) Unit
  exactDelta : Child (List AccountInfo × TransferPlan) Unit
  writeNewPage : Child (AccountInfo × B32 × UInt64 × UInt64 × List Digest) Unit
  appendRoots : Child (AccountInfo × Header × List Digest) Unit

/-- A Rust subslice (panic on failed bounds). -/
def subAccounts (xs : List AccountInfo) (start count : Nat) : Computation (List AccountInfo) :=
  if start + count ≤ xs.length then Computation.pure ((xs.drop start).take count)
  else fun _ _ o => o = ⟨.abort, []⟩

def chooseMode (C : Children) (a : Args) (laneAccount current : AccountInfo)
    (lane : LaneState) (append : Append) : Computation (DepositMode × Nat × Nat) := do
  let currentLocation := C.rootLocation lane.tree.next_leaf_index
  let nextLocation := C.rootLocation append.root_sequence
  let fresh ← if lane.tree.next_leaf_index == 0 then do
      let s ← get
      if current.owner == SYSTEM_PROGRAM && (s.bytes current).isEmpty then Computation.pure true
      else C.zeroedPage.call (current, a.program)
    else Computation.pure false
  if fresh then
    let (expected,bump) ← C.pageAddress.call (a.program,laneAccount.key,0)
    let prep ← C.freshPda.call (current,a.program,expected,PAGE_BYTES)
    Computation.pure (.genesis prep bump,3,10)
  else if nextLocation.page_number == currentLocation.page_number then
    let header ← C.currentPage.call (a.program,laneAccount,current,lane,true,none)
    Computation.pure (.same header,3,8)
  else
    let header ← C.currentPage.call (a.program,laneAccount,current,lane,false,none)
    check (header.filled != HISTORY_CAPACITY) (.custom 0x41532003)
    let next ← accountAt a.accounts 3
    let (expected,bump) ← C.pageAddress.call (a.program,laneAccount.key,nextLocation.page_number)
    let prep ← C.freshPda.call (next,a.program,expected,PAGE_BYTES)
    Computation.pure (.rollover prep nextLocation.page_number bump,4,11)

def preparePage (C : Children) (a : Args) (laneAccount current : AccountInfo)
    (mode : DepositMode) : Computation AccountInfo := do
  match mode with
  | .same _ => Computation.pure current
  | .genesis prep bump =>
    let payer ← index a.accounts 8
    let system ← index a.accounts 9
    C.payerAndSystem.call (payer,system)
    if prep == .createOrAllocateSystemOwned then
      C.createPda.call (payer,current,system,PAGE_BYTES,a.program,
        [PAGE_SEED,laneAccount.key.bytes,u64le 0,[bump]])
    C.programOwnedZeroed.call (current,a.program,PAGE_BYTES,a.rent)
    Computation.pure current
  | .rollover prep page bump =>
    let next ← index a.accounts 3
    let payer ← index a.accounts 9
    let system ← index a.accounts 10
    C.payerAndSystem.call (payer,system)
    if prep == .createOrAllocateSystemOwned then
      C.createPda.call (payer,next,system,PAGE_BYTES,a.program,
        [PAGE_SEED,laneAccount.key.bytes,u64le page,[bump]])
    C.programOwnedZeroed.call (next,a.program,PAGE_BYTES,a.rent)
    Computation.pure next

def Ref (C : Children) (runtime : Runtime) (a : Args) : Computation Unit := do
  let request ← C.decodeDeposit.call a.data
  let masterAccount ← accountAt a.accounts 0
  let laneAccount ← accountAt a.accounts 1
  let current ← accountAt a.accounts 2
  let master ← C.decodeMaster.call (a.program,masterAccount)
  let commitment ← C.noteCommitment.call (request.owner_key,request.amount,master.identity.asset_id,request.salt)
  let laneId ← C.depositLane.call commitment
  check ((master.initialized_lane_mask &&& (1 <<< laneId)) == 0) (.custom 0x41532003)
  let lane ← C.decodeLane.call (a.program,masterAccount.key,laneId,laneAccount)
  check (decide (lane.tree.next_leaf_index ≥ PAIR_CAPACITY)) (.custom 0x41532004)
  let witness ← C.singleOutput.call commitment
  let leaf ← C.leafDigest.call witness
  let (append,image) ← C.prepareAppend.call (lane,laneId,leaf)
  let (mode,tokenStart,expected) ← chooseMode C a laneAccount current lane append
  C.exactCount.call (a.accounts,expected)
  C.uniqueAccounts.call a.accounts
  let tokens ← subAccounts a.accounts tokenStart 5
  let tokenProgram ← index tokens 4
  C.tokenProgram.call tokenProgram
  let plan ← C.planTransfer.call (a.program,masterAccount.key,master.identity,tokens,request.amount)
  let infos ← C.transferInfos.call tokens
  let page ← preparePage C a laneAccount current mode
  guardScope laneAccount .exclusive fun _ =>
    guardScope page .exclusive fun _ => do
      runtime.invoke ⟨plan.instruction,infos,[]⟩
      C.exactDelta.call (tokens,plan)
      write laneAccount image
      match mode with
      | .genesis _ _ => C.writeNewPage.call (page,laneAccount.key,0,0,[lane.tree.root,append.root])
      | .same header => C.appendRoots.call (page,header,[append.root])
      | .rollover _ number _ => C.writeNewPage.call (page,laneAccount.key,number,append.root_sequence,[append.root])

def RowSpec (C : Children) (runtime : Runtime)
    (impl : Args → State → Env → Observation Unit) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C runtime) impl
end PCM_POOL_328
