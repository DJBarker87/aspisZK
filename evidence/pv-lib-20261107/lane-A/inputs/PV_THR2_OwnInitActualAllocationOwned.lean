import PV_THR2_OwnInitAllocationFrontier
import PV_THR2_OwnInitHandlerCasesAtState
import PV_THR2_OwnInitDeliveredWorld
import PV_THR2_SourceOwnership
set_option autoImplicit false
noncomputable section
namespace PV_THR2_OwnInitActualAllocationOwned
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap
open PV_OWN2_Codec PV_OWN2_FreshAllocation PV_OWN2_FreshAllocationRefinement
/-- Conditional on amended translator acceptance. Apply the existing full
allocation law to the ACTUAL selected pre-state, without requiring a canonical
prepared store. Ready, cell, decoding and descriptor cases are internal source
association obligations, never proposed closure hypotheses. All allocator
answers and all actual source reply worlds remain. -/
theorem all (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (granted : GrantedRegions)
    (H : PV_STX2_Native.Request Data → OWNER → Reply OWNER PV_RJ4IDB.NativeEvent Data)
    (q : PV_THR2_IntrinsicState.State OWNER PV_RJ4IDB.NativeEvent) (c : Config)
    (id : Nat) (payload : Data) (words : PV_OWN2_ThreadInitLayout.InitWords)
    (running : q.current.status = .running c)
    (ready : PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 129) c)
    (cell : c.store.cells ⟨c.frame.activation,46,[]⟩ = some payload)
    (decoded : PV_THR2_OwnInitSourceCodec.decode payload = some words)
    (child : P PV_THR2_Source361InitChildren.fnAllocationFull = none)
    (frame : PV_THR2_OwnUniformReceiverFrame.Frame c.frame.activation id
      (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8) q.current.world)
    (valid : FreshAllocationValidity' resources granted q.current.world) :
    let handler := PV_THR2_OwnInitAllocationHandler.handler resources encode H
    let r := handler (.child PV_THR2_Source361InitChildren.fnAllocationFull
      c.store.nextActivation [payload]) q.current.world
    let post := PV_THR2_OwnInitInterpreter.advance C K P resources encode H
      (PV_THR2_Source361AllocationFull.steps C q) q
    PV_THR2_OwnInitAllocationCases.Outcome ⟨c.frame.activation,[45]⟩ words
      (resources (.malloc 24) (world q.current.world)).answer {r with world := post.current.world} ∧
    (∀ cid ch, receiver q.current.world ⟨c.frame.activation,[39]⟩ = some (cid,ch) →
      PV_OWN2_ExportContracts.SourceOwnership
        (Attr := Unit) (Data := Unit) (Native := Unit) (IoError := Unit)
        (OsString := Unit) (Scope := Unit) resources encode granted
        ⟨c.frame.activation,[39]⟩ ⟨c.frame.activation,[45]⟩ cid q.current.world.next ch
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8)) := by
  intro handler r post
  have run := PV_THR2_OwnInitAllocationFrontier.run C K P resources encode H q child
  change post = PV_THR2_Source361AllocationFull.after C handler q at run
  have moved : operands C q.current.world c.frame.activation
      PV_THR2_Source361AllocationFull.source.2.2.2.1 c.store =
      some ([payload],write c.store ⟨c.frame.activation,46,[]⟩ none) := by
    change operands C q.current.world c.frame.activation [.move (.local 46)] c.store = _
    simp only [operands,operand,PV_STX2_Store.read,locate,cell,writeAddress,
      Bind.bind,Option.bind_some,Pure.pure]
  have actualWorld : post.current.world = r.world := by
    rw [run]
    simp only [PV_THR2_Source361AllocationFull.after,PV_THR2_IntrinsicAtContinuation.after,
      running,if_pos ready,PV_THR2_Source361AllocationFull.finish,
      PV_THR2_IntrinsicChildCall.after,moved]
    apply PV_THR2_OwnInitDeliveredWorld.world
  have own := PV_THR2_OwnInitHandlerCasesAtState.allocation q.current.world c.frame.activation id
    c.store.nextActivation resources encode granted payload words H decoded frame valid
  change PV_THR2_OwnInitAllocationCases.Outcome _ _ _ r at own
  have same : {r with world := post.current.world} = r := by rw [actualWorld]
  constructor
  · rw [same]
    exact own
  · exact PV_THR2_SourceOwnership.source_export C c q.current.world q.current.world
      resources encode granted
#print axioms all
end PV_THR2_OwnInitActualAllocationOwned
