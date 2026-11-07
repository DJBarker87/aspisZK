import PV_THR2_OwnInitActualAllocationOwned
import PV_THR2_OwnInitAllocationBridgedFrontier
import PV_THR2_OwnInitBridgedPinned
import PV_THR2_OwnInitBridgedAdequacy
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitActualAllocationOwned
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_EVHB_RawVecOwner
open PV_OWN2_Codec PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement
/-- D911 replacement at the actual source constructor. Decode success and the
selected receiver are derived from the callback allocation and actual14320
registry action, including arbitrary intervening native backend effects.
The local world/cell associations must be supplied by the caller trace; they
are not new OwnInit premises. All14756 resource answers are retained.
InterpretationAdequacy14756 remains a named typed-representation / binary-
structural obligation for transporting this model result to source execution;
it is not a decoder, value, success, endpoint or trust hypothesis. -/
theorem allBridged (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program)
    (callbackResources : Resources) (callbackEncode : Encode)
    (allocationStore sourceStore : Store Data) (w : OWNER) (handle data : Pointer)
    (a : Nat) (parents : List Frame) (backend : PV_STX_World.World)
    (loadBias : Pointer) (siteIndex : Fin 11)
    (resources : Resources) (encode : Encode) (granted : GrantedRegions)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (q : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent) (c : Config)
    (answer : (callbackResources (.malloc PV_OWN2_ClientLayout.layout.callbackSize)
      (world w)).answer = .returned (.ok data.val)) (nonnull : data.val ≠ 0)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 129) c)
    (activation : c.frame.activation = a)
    (actualWorld : q.current.world = withWorld
      (PV_THR2_BindingRegister.register
        ⟨{activation := a,remaining := PV_THR2_F361.live.body.drop 113},parents,sourceStore⟩
        (PV_THR2_ClosureBoxAllocation.reply callbackResources callbackEncode allocationStore w).world) backend)
    (cell : c.store.cells ⟨c.frame.activation,46,[]⟩ = some
      (PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
        [PV_THR2_OwnInitPointerCodec.encode handle,
          PV_THR2_BoxDynRepresentationBridge.callback
            (PV_THR2_BoxDynBinaryLayout.symbols loadBias siteIndex)
            (PV_THR2_PacketBoxBacking.root allocationStore)]))
    (child : P PV_THR2_Source361InitChildren.fnAllocationFull = none)
    (valid : FreshAllocationValidity' resources granted q.current.world) :
    let payload := PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
      [PV_THR2_OwnInitPointerCodec.encode handle,
        PV_THR2_BoxDynRepresentationBridge.callback
          (PV_THR2_BoxDynBinaryLayout.symbols loadBias siteIndex)
          (PV_THR2_PacketBoxBacking.root allocationStore)]
    let words : PV_OWN2_ThreadInitLayout.InitWords :=
      ⟨handle,data,PV_THR2_BoxDynBinaryLayout.runtimeAddress loadBias siteIndex⟩
    let handler := PV_THR2_OwnInitAllocationHandlerBridged.handler resources encode H
    let r := handler (.child PV_THR2_Source361InitChildren.fnAllocationFull
      c.store.nextActivation [payload]) q.current.world
    let post := PV_THR2_OwnInitInterpreterBridged.advance C K P resources encode H
      (PV_THR2_Source361AllocationFull.steps C q) q
    PV_THR2_OwnInitAllocationCases.Outcome ⟨c.frame.activation,[45]⟩ words
      (resources (.malloc 24) (world q.current.world)).answer {r with world := post.current.world} ∧
    (∀ cid ch, receiver q.current.world ⟨c.frame.activation,[39]⟩ = some (cid,ch) →
      PV_OWN2_ExportContracts.SourceOwnership
        (Attr := Unit) (Data := Unit) (Native := Unit) (IoError := Unit)
        (OsString := Unit) (Scope := Unit) resources encode granted
        ⟨c.frame.activation,[39]⟩ ⟨c.frame.activation,[45]⟩ cid q.current.world.next ch
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8)) := by
  intro payload words handler r post
  have bridge := PV_THR2_OwnInitBridgedPinned.actual14756 callbackResources callbackEncode
    allocationStore sourceStore w handle data a c.store.nextActivation parents backend
    loadBias siteIndex resources encode H answer nonnull
  have decoded : PV_THR2_OwnInitSourceCodec.decodeBridged q.current.world payload = some words := by
    rw [actualWorld]
    exact bridge.1
  have frame := PV_THR2_OwnUniformReceiverFrame.withWorld
    (PV_THR2_OwnUniformReceiverFrame.registered sourceStore a parents
      (PV_THR2_ClosureBoxAllocation.reply callbackResources callbackEncode allocationStore w).world).2 backend
  rw [← actualWorld,← activation] at frame
  have run := PV_THR2_OwnInitAllocationBridgedFrontier.run C K P resources encode H q child
  change post = PV_THR2_Source361AllocationFull.after C handler q at run
  have moved : operands C q.current.world c.frame.activation
      PV_THR2_Source361AllocationFull.source.2.2.2.1 c.store =
      some ([payload],write c.store ⟨c.frame.activation,46,[]⟩ none) := by
    change operands C q.current.world c.frame.activation [.move (.local 46)] c.store = _
    simp only [operands,operand,PV_STX2_Store.read,locate,cell,writeAddress,
      Bind.bind,Option.bind_some,Pure.pure]
    rfl
  have deliveredWorld : post.current.world = r.world := by
    rw [run]
    simp only [PV_THR2_Source361AllocationFull.after,PV_THR2_IntrinsicAtContinuation.after,
      running,if_pos ready,PV_THR2_Source361AllocationFull.finish,
      PV_THR2_IntrinsicChildCall.after,moved]
    apply PV_THR2_OwnInitDeliveredWorld.world
  have selected := PV_THR2_OwnInitAllocationSelection.selected frame
  have own := PV_THR2_OwnInitAllocationCasesAtState.all q.current.world c.frame.activation _
    resources encode granted words frame valid
  have interpreted : r = PV_THR2_OwnInitAllocationReply.reply resources encode q.current.world
      (PV_THR2_ClosureBoxAllocation.reply callbackResources callbackEncode allocationStore w).world.next
      (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) words := by
    simp only [r,handler,PV_THR2_OwnInitAllocationHandlerBridged.handler,ite_true,
      decoded,selected.1,frame.header]
  constructor
  · have same : {r with world := post.current.world} = r := by rw [deliveredWorld]
    rw [same,interpreted]
    exact own
  · exact PV_THR2_SourceOwnership.source_export C c q.current.world q.current.world
      resources encode granted
#print axioms allBridged
end PV_THR2_OwnInitActualAllocationOwned
