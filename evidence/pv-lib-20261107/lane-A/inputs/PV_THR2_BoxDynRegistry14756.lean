import PV_THR2_ClosureBoxRegistry
import PV_THR2_BindingRegister
import PV_THR2_OwnInitAllocationHandlerBridged
set_option autoImplicit false
noncomputable section
namespace PV_THR2_BoxDynRegistry14756
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner PV_OWN2_Codec
open scoped Classical
/-- The actual13923 allocation establishes both components, including the
minted next-id. No selected receiver or pointer association is a hypothesis. -/
theorem allocation_receiver (resources : Resources) (encode : Encode) (s : Store Data)
    (w : OWNER) (p : Pointer)
    (answer : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize)
      (world w)).answer = .returned (.ok p.val)) (nonnull : p.val ≠ 0) :
    let out := (PV_THR2_ClosureBoxAllocation.reply resources encode s w).world
    receiver out (PV_THR2_BoxDynRepresentationBridge.sourcePlace (PV_THR2_PacketBoxBacking.root s)) =
      some (w.next,capacityStore (pointerStore
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_ClosureBoxAllocation.shape
          PV_OWN2_ClientLayout.layout.alignment) p.val) 1) ∧
    out.next = w.next+1 := by
  dsimp only
  unfold PV_THR2_ClosureBoxAllocation.reply
  have ans := PV_THR2_PacketBoxResource.answer resources encode s w
    PV_THR2_ClosureBoxAllocation.shape PV_OWN2_ClientLayout.layout.alignment
  rw [PV_THR2_ClosureBoxAllocation.request_size,answer] at ans
  rw [PV_THR2_PacketBoxReply.returned _ _ _ _ _ ans nonnull]
  have places : (PV_THR2_PacketBoxResource.reply resources encode s w
      PV_THR2_ClosureBoxAllocation.shape PV_OWN2_ClientLayout.layout.alignment).world.places
      (PV_THR2_BoxDynRepresentationBridge.sourcePlace (PV_THR2_PacketBoxBacking.root s)) =
      some w.next := by
    rw [PV_THR2_PacketBoxResource.all]
    simp only [PV_THR2_PacketBoxRegister.backend,PV_THR2_ClosureBoxAllocation.request_size,
      answer,if_neg nonnull]
    change (if (⟨s.nextActivation,[1]⟩ : PV_EVHB_OwnerMachine.Place) =
      ⟨s.nextActivation,[1]⟩ then some w.next else _) = _
    rw [if_pos rfl]
  constructor
  · simp only [receiver,places,Option.bind_some,install_lookup,Option.map_some]
  · rw [PV_THR2_PacketBoxResource.all]
    simp only [PV_THR2_PacketBoxRegister.backend,PV_THR2_ClosureBoxAllocation.request_size,
      answer,if_neg nonnull]
    rfl

/-- Generic source registration frames an existing descriptor. The id
separation is established by allocation_receiver in the actual application. -/
theorem receiver_new (w : OWNER) (old target : PV_EVHB_OwnerMachine.Place)
    (id : Nat) (h : Header) (shape : R1Z.PV_FXM_ReserveWorld.Shape) (align : Nat)
    (selected : receiver w old = some (id,h)) (different : old ≠ target)
    (fresh : id ≠ w.next) :
    receiver (PV_EVHB_SourceLifetimes.newAt w target shape align) old = some (id,h) := by
  unfold receiver at selected ⊢
  cases slot : w.places old with
  | none => simp only [slot,Option.bind_none] at selected; cases selected
  | some oid =>
    simp only [slot,Option.bind_some] at selected
    cases header : lookup w.world oid with
    | none => simp only [header,Option.map_none] at selected; cases selected
    | some oh =>
      simp only [header,Option.map_some,Option.some.injEq,Prod.mk.injEq] at selected
      rcases selected with ⟨rfl,rfl⟩
      simp only [PV_EVHB_SourceLifetimes.newAt,if_neg different,slot,Option.bind_some,
        lookup_other _ _ _ _ fresh,header,Option.map_some]

/-- Actual14320 registration, followed by arbitrary slice10 native backend
activity (including214), preserves the callback allocation's runtime address.
The two source places are distinct by their emitted locals1 and45; the
registry ids are distinct by the actual allocation's mint. -/
theorem registered_binding (resources : Resources) (encode : Encode)
    (allocationStore sourceStore : Store Data) (w : OWNER) (p : Pointer)
    (a : Nat) (parents : List Frame) (backend : PV_STX_World.World)
    (answer : (resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize)
      (world w)).answer = .returned (.ok p.val)) (nonnull : p.val ≠ 0) :
    let allocated := (PV_THR2_ClosureBoxAllocation.reply resources encode allocationStore w).world
    let c : Config := ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 113},parents,sourceStore⟩
    let registered := PV_THR2_BindingRegister.register c allocated
    PV_THR2_BoxDynRepresentationBridge.runtime (withWorld registered backend)
      (PV_THR2_PacketBoxBacking.root allocationStore) = some p := by
  intro allocated c registered
  have previous := allocation_receiver resources encode allocationStore w p answer nonnull
  have different : PV_THR2_BoxDynRepresentationBridge.sourcePlace
      (PV_THR2_PacketBoxBacking.root allocationStore) ≠
      (⟨a,[45]⟩ : PV_EVHB_OwnerMachine.Place) := by
    intro equal
    have fields := congrArg PV_EVHB_SourceLifetimes.Place.fields equal
    cases fields
  have fresh : w.next ≠ allocated.next := by
    change w.next ≠ (PV_THR2_ClosureBoxAllocation.reply resources encode allocationStore w).world.next
    rw [previous.2]
    exact Nat.ne_of_lt (Nat.lt_succ_self _)
  have retained := receiver_new allocated _ ⟨a,[45]⟩ w.next _
    PV_THR2_BoxRegister.shape 8 previous.1 different fresh
  have reg : registered = PV_EVHB_SourceLifetimes.newAt allocated ⟨a,[45]⟩
      PV_THR2_BoxRegister.shape 8 := by
    unfold registered PV_THR2_BindingRegister.register
    rw [PV_THR2_LocalBinding.generated]
    rfl
  rw [← reg] at retained
  change (receiver registered (PV_THR2_BoxDynRepresentationBridge.sourcePlace
      (PV_THR2_PacketBoxBacking.root allocationStore)) >>= fun pair =>
        PV_THR2_OwnInitPointerCodec.decode (.number pair.2.pointer)) = _
  rw [retained]
  simp only [Bind.bind,Option.bind_some,capacityStore,pointerStore,
    PV_THR2_OwnInitPointerCodec.decode,dif_pos p.isLt]
#print axioms allocation_receiver
#print axioms receiver_new
#print axioms registered_binding
end PV_THR2_BoxDynRegistry14756
