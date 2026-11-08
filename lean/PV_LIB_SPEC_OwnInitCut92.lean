import PV_LIB_SPEC_CallbackCutCheck
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_OwnInitCut92
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_OwnInitFull.Input
abbrev Representation := PV_LIB_SPEC_OwnInitFull.Representation
abbrev entry := PV_LIB_SPEC_OwnInitFull.entry
/-- Approved SPEC-C5 replacement. All historical conjuncts are retained;
only the source callback allocation cut changes from94 to92. The store is
before issuance of13923, hence its nextActivation names the backing. This
statement alone supplies no run or successful native schedule. -/
def AllocationWitness (table : FullStoreActionTable) (r : Runtime)
    (R : Representation) (i : Input) (trace : Nat → State) (n : Nat) : Prop :=
  ∃ (callbackIndex registrationIndex readyIndex pollIndex : Nat)
    (callback registration ready poll : Config)
    (wait : PV_STX2_Native.Waiting Data) (requestActivation : Nat)
    (handle data : PV_OWN2_Codec.Pointer) (backend : PV_STX_World.World),
    callbackIndex < registrationIndex ∧ registrationIndex < readyIndex ∧
    readyIndex+1 = pollIndex ∧ n = pollIndex+1 ∧
    (trace callbackIndex).current.status = .running callback ∧
    callback.frame.remaining = PV_THR2_F361.live.body.drop 92 ∧
    (trace registrationIndex).current.status = .running registration ∧
    registration.frame.activation = callback.frame.activation ∧
    registration.frame.remaining = PV_THR2_F361.live.body.drop 113 ∧
    (trace readyIndex).current.status = .running ready ∧
    ready.frame.activation = callback.frame.activation ∧
    PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 129) ready ∧
    (trace pollIndex).current.status = .running poll ∧
    poll.frame.activation = ready.frame.activation ∧ poll.frame.waiting = some wait ∧
    let payload := PV_THR2_KeyValues.pack PV_THR2_InitAggregate.kind
      [PV_THR2_OwnInitPointerCodec.encode handle,
        PV_THR2_BoxDynRepresentationBridge.callback
          (PV_THR2_BoxDynBinaryLayout.symbols R.loadBias R.siteIndex)
          (PV_THR2_PacketBoxBacking.root callback.store)]
    let words : PV_OWN2_ThreadInitLayout.InitWords :=
      ⟨handle,data,PV_THR2_BoxDynBinaryLayout.runtimeAddress R.loadBias R.siteIndex⟩
    wait.request = .child PV_THR2_Source361InitChildren.fnAllocationFull requestActivation [payload] ∧
    ready.store.cells ⟨ready.frame.activation,46,[]⟩ = some payload ∧
    (r.resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize)
      (world (trace callbackIndex).current.world)).answer = .returned (.ok data.val) ∧
    data.val ≠ 0 ∧
    (trace readyIndex).current.world = withWorld
      (PV_THR2_BindingRegister.register registration
        (PV_THR2_ClosureBoxAllocation.reply r.resources r.encode callback.store
          (trace callbackIndex).current.world).world) backend ∧
    PV_THR2_OwnInitSourceCodec.decodeBridged (trace readyIndex).current.world payload = some words ∧
    let reply := PV_THR2_OwnInitAllocationHandlerBridged.handler r.resources r.encode r.native
      wait.request (trace pollIndex).current.world
    PV_THR2_OwnInitAllocationCases.Outcome ⟨ready.frame.activation,[45]⟩ words
      (r.resources (.malloc 24) (world (trace pollIndex).current.world)).answer
      {reply with world := (trace n).current.world} ∧
    (∀ value, reply.answer = .returned (.ok value) →
      ∃ after, (trace n).current.status = .running after ∧
        after.store.cells ⟨ready.frame.activation,45,[]⟩ = some value) ∧
    (∀ cid ch, receiver (trace readyIndex).current.world ⟨ready.frame.activation,[39]⟩ = some (cid,ch) →
      PV_OWN2_ExportContracts.SourceOwnership
        (Attr := Unit) (Data := Unit) (Native := Unit) (IoError := Unit)
        (OsString := Unit) (Scope := Unit) r.resources r.encode R.granted
        ⟨ready.frame.activation,[39]⟩ ⟨ready.frame.activation,[45]⟩ cid
        (trace readyIndex).current.world.next ch
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8)) ∧
    (∀ k, k ≤ n → trace k = run (PV_LIB_SPEC_Full.source table r) k (entry i))

theorem source_cut :
    PV_THR2_F361.live.body[92]? = some PV_THR2_F361.node125 :=
  PV_LIB_SPEC_CallbackCutCheck.actual_allocation

theorem source_site :
    (PV_LIB_SPEC_CallbackCutCheck.firstSite (PV_THR2_F361.live.body.drop 92)).map Site.statement = some 13923 :=
  PV_LIB_SPEC_CallbackCutCheck.actual_site

#print axioms Input
#print axioms Representation
#print axioms entry
#print axioms AllocationWitness
#print axioms source_cut
#print axioms source_site
end PV_LIB_SPEC_OwnInitCut92
