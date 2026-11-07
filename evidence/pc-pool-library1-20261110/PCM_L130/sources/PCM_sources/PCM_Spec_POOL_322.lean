import PCM_Witness
import PCM_StepLaws
import PCM_Carriers
import PCM_Spec_POOL_328
set_option autoImplicit false
namespace PCM_POOL_322
open RSL PCM PCM.Computation
abbrev Args := B32 × List AccountInfo × LaneState × Bool × Hints
structure Children where
  zeroedPage : Child (AccountInfo × B32) Bool
  address : Child (B32 × B32 × UInt64 × UInt8 × AccountInfo) Unit
  programAccount : Child (AccountInfo × B32 × Bool) Unit
  currentPage : Child (B32 × AccountInfo × AccountInfo × LaneState × Bool × Option UInt8) Header
  exactCount : Child (List AccountInfo × Nat) Unit
  uniqueAccounts : Child (List AccountInfo) Unit

def Ref (C : Children) (a : Args) : Computation SpendLayout := do
  let (program,accounts,lane,withdrawal,hints) := a
  check (decide (lane.tree.next_leaf_index ≥ PAIR_CAPACITY)) (.custom 0x41532004)
  let laneAccount ← accountAt accounts 2
  let current ← accountAt accounts 3
  let currentPage := lane.tree.next_leaf_index / 256
  let nextPage := (lane.tree.next_leaf_index + 1) / 256
  let genesis ← if lane.tree.next_leaf_index == 0 then C.zeroedPage.call (current,program)
    else Computation.pure false
  let (page,cursor) ← if genesis then do
      C.address.call (program,laneAccount.key,0,hints.current_page,current)
      C.programAccount.call (current,program,true)
      Computation.pure (SpendPage.genesis,4)
    else if currentPage == nextPage then do
      let header ← C.currentPage.call (program,laneAccount,current,lane,true,some hints.current_page)
      Computation.pure (.same header,4)
    else do
      let header ← C.currentPage.call (program,laneAccount,current,lane,false,some hints.current_page)
      check (header.filled != HISTORY_CAPACITY) (.custom 0x41532003)
      let next ← accountAt accounts 4
      C.address.call (program,laneAccount.key,nextPage,hints.next_page,next)
      let zeroed ← C.zeroedPage.call (next,program)
      check (!zeroed || !next.is_writable) (.custom 0x41532035)
      Computation.pure (.rollover 4 nextPage,5)
  check (cursor == 4 && hints.next_page != 0) .invalidInstructionData
  let marker := cursor
  let payer := cursor+1
  let system := cursor+2
  let registry := cursor+3
  let verifier := cursor+5
  let proof := cursor+6
  let token := cursor+7
  let expected := token + if withdrawal then 5 else 0
  C.exactCount.call (accounts,expected+1)
  C.uniqueAccounts.call accounts
  Computation.pure ⟨page,marker,payer,system,registry,verifier,proof,some expected,token⟩

def RowSpec (C : Children) (impl : Args → State → Env → Observation SpendLayout) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

theorem rejects_wrong_error (C : Children) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  let a : Args := ⟨zero32,[],{ PCM.lane0 with tree := { PCM.lane0.tree with next_leaf_index := PAIR_CAPACITY } },false,⟨0,0,0,0⟩⟩
  apply PCM.rejects_error (fun _ : Args => True) (Ref C) a (.custom 0x41532004) .invalidArgument trivial
  · unfold Ref
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_322
