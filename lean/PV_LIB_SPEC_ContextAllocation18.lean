import PV_LIB_SPEC_ContextPost18
import PV_LIB_SPEC_OwnInitCut92
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ContextAllocation18
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
abbrev Input := PV_LIB_SPEC_OwnInitCut92.Input
abbrev Representation := PV_LIB_SPEC_OwnInitCut92.Representation
abbrev entry := PV_LIB_SPEC_OwnInitCut92.entry
/-- SPEC-C14: same cut92/registration/ready/InitPoll ownership conclusion.
Both resource instances come from actual origins on the one execution. The
callback world is the computed sparse native reply, not a total byte image.
All facts here are POST conclusions, never row Pre or successful-reply inputs. -/
def AllocationWitness (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (R : Representation) (i : Input) (issued : List Issued) (consumed : List Context) (trace : Nat → Execution) (n : Nat) : Prop :=
  ∃ (callbackIndex registrationIndex readyIndex pollIndex : Nat)
    (callback registration ready poll : Config)
    (wait : PV_STX2_Native.Waiting Data) (requestActivation : Nat)
    (handle data : PV_OWN2_Codec.Pointer) (backend : PV_STX_World.World)
    (callbackPollIndex : Nat) (callbackPoll : Config)
    (callbackWait : PV_STX2_Native.Waiting Data) (callbackCtx pollCtx : Context),
    callbackIndex < callbackPollIndex ∧ callbackPollIndex < registrationIndex ∧
    (trace callbackPollIndex).state.current.status = .running callbackPoll ∧
    PV_LIB_SPEC_ControlRuntime.ordinary (trace callbackPollIndex).state = some (callbackPoll,callbackWait) ∧
    PV_LIB_SPEC_ResourceHistory.context (trace callbackPollIndex) callbackPoll callbackWait = some callbackCtx ∧
    callbackCtx.site.function = 361 ∧ callbackCtx.site.statement = 13923 ∧
    PV_LIB_SPEC_ResourceHistory.context (trace pollIndex) poll wait = some pollCtx ∧
    pollCtx.site.function = 361 ∧ pollCtx.site.statement = 14756 ∧
    let callbackParameters : Parameters := {p with resources :=
      PV_LIB_SPEC_ResourceHistory.allocationResources p.environment callbackCtx}
    let pollParameters : Parameters := {p with resources :=
      PV_LIB_SPEC_ResourceHistory.allocationResources p.environment pollCtx}
    let callbackReply := PV_LIB_SPEC_ReachedNative14.handler cut callbackParameters callbackPoll
      callbackWait.request (trace callbackPollIndex).state.current.world
    (trace callbackIndex).state.current.world = (trace callbackPollIndex).state.current.world ∧
    (trace (callbackPollIndex+1)).consumed = callbackCtx :: (trace callbackPollIndex).consumed ∧
    (trace (pollIndex+1)).consumed = pollCtx :: (trace pollIndex).consumed ∧
    callbackIndex < registrationIndex ∧ registrationIndex < readyIndex ∧
    readyIndex+1 = pollIndex ∧ n = pollIndex+1 ∧
    (trace callbackIndex).state.current.status = .running callback ∧
    callback.frame.remaining = PV_THR2_F361.live.body.drop 92 ∧
    (trace registrationIndex).state.current.status = .running registration ∧
    registration.frame.activation = callback.frame.activation ∧
    registration.frame.remaining = PV_THR2_F361.live.body.drop 113 ∧
    (trace readyIndex).state.current.status = .running ready ∧
    ready.frame.activation = callback.frame.activation ∧
    PV_THR2_IntrinsicAtContinuation.Ready (PV_THR2_F361.live.body.drop 129) ready ∧
    (trace pollIndex).state.current.status = .running poll ∧
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
    (callbackParameters.resources (.malloc PV_OWN2_ClientLayout.layout.callbackSize)
      (world (trace callbackIndex).state.current.world)).answer = .returned (.ok data.val) ∧
    data.val ≠ 0 ∧
    (trace readyIndex).state.current.world = withWorld
      (PV_THR2_BindingRegister.register registration
        callbackReply.world) backend ∧
    PV_THR2_OwnInitSourceCodec.decodeBridged (trace readyIndex).state.current.world payload = some words ∧
    let reply := PV_THR2_OwnInitAllocationHandlerBridged.handler pollParameters.resources pollParameters.encode
      (PV_LIB_SPEC_ReachedNative14.handler cut pollParameters poll)
      wait.request (trace pollIndex).state.current.world
    PV_THR2_OwnInitAllocationCases.Outcome ⟨ready.frame.activation,[45]⟩ words
      (pollParameters.resources (.malloc 24) (world (trace pollIndex).state.current.world)).answer
      {reply with world := (trace n).state.current.world} ∧
    (∀ value, reply.answer = .returned (.ok value) →
      ∃ after, (trace n).state.current.status = .running after ∧
        after.store.cells ⟨ready.frame.activation,45,[]⟩ = some value) ∧
    (∀ cid ch, receiver (trace readyIndex).state.current.world ⟨ready.frame.activation,[39]⟩ = some (cid,ch) →
      PV_OWN2_ExportContracts.SourceOwnership
        (Attr := Unit) (Data := Unit) (Native := Unit) (IoError := Unit)
        (OsString := Unit) (Scope := Unit) pollParameters.resources pollParameters.encode R.granted
        ⟨ready.frame.activation,[39]⟩ ⟨ready.frame.activation,[45]⟩ cid
        (trace readyIndex).state.current.world.next ch
        (PV_EVHB_SourceLifetimes.emptyHeader PV_THR2_BoxRegister.shape 8)) ∧
    (∀ k, k ≤ n → trace k = PV_LIB_SPEC_ContextMachine18.run (PV_LIB_SPEC_ContextMachine18.source cut p) k
      (PV_LIB_SPEC_ContextMachine18.start (entry i) issued consumed))

#print axioms Input
#print axioms Representation
#print axioms entry
#print axioms AllocationWitness
end PV_LIB_SPEC_ContextAllocation18
