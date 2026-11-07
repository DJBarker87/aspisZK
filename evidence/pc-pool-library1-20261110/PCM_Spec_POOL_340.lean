import PCM_Witness
import PCM_StepLaws
import PCM_Carriers
set_option autoImplicit false
namespace PCM_POOL_340
open RSL PCM PCM.Computation
abbrev Args := B32 × AccountInfo × AccountInfo × LaneState × Bool × Option UInt8
structure Children where
  programAccount : Child (AccountInfo × B32 × Bool) Unit
  addressWithBump : Child (B32 × B32 × UInt64 × UInt8 × AccountInfo) Unit
  address : Child (B32 × B32 × UInt64 × AccountInfo) Unit
  validatePage : Child (Bytes × B32 × UInt64) Header
  retainedRoot : Child (Bytes × Header × UInt64) Digest

def Ref (C : Children) (a : Args) : Computation Header := do
  let (program,laneAccount,page,lane,writable,hint) := a
  let pageNumber := lane.tree.next_leaf_index / 256
  let slot := (lane.tree.next_leaf_index % 256).toUInt16
  C.programAccount.call (page,program,writable)
  check page.is_signer .invalidAccountData
  match hint with
  | some bump => C.addressWithBump.call (program,laneAccount.key,pageNumber,bump,page)
  | none => C.address.call (program,laneAccount.key,pageNumber,page)
  guardScope page .shared fun _ => do
    let s ← get
    let data := s.bytes page
    let header ← C.validatePage.call (data,laneAccount.key,pageNumber)
    check (header.filled != slot + 1) (.custom 0x41532003)
    let root ← C.retainedRoot.call (data,header,lane.tree.next_leaf_index)
    check (root != lane.tree.root) (.custom 0x41532003)
    Computation.pure header

def RowSpec (C : Children) (impl : Args → State → Env → Observation Header) : Prop :=
  PCM.RowSpec (fun _ => True) (Ref C) impl

theorem rejects_wrong_error (C : Children) (a : Args)
    (early : C.programAccount.call (a.2.2.1,a.1,a.2.2.2.2.1) = Computation.throw .invalidAccountData) :
    ¬ RowSpec C (fun _ s _ => ⟨.ret (.error .invalidArgument,s),[]⟩) := by
  apply PCM.rejects_error (fun _ : Args => True) (Ref C) a .invalidAccountData .invalidArgument trivial
  · rcases a with ⟨program,laneAccount,page,lane,writable,hint⟩
    unfold Ref
    dsimp only at early ⊢
    rw [early]
    exact PCM.Computation.bind_throw _ _
  · intro h; cases h
#print axioms rejects_wrong_error
end PCM_POOL_340
