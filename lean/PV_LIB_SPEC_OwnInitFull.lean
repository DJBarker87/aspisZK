import PV_LIB_SPEC_F0Full
set_option autoImplicit false
noncomputable section

namespace PV_LIB_SPEC_Frontier
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
/-- A consumed native pending reply is recognized on the ACTUAL interpreted
transition, including bridged allocation and operator handlers. Inspecting
m.handler alone would inspect the discarded fallback at14756. BODY push and
intrinsic invocation are explicitly excluded; waiting/unwinding/completion
control is checked before and after administration. -/
def Pending (m : Machine) (q : State) : Prop :=
  ∃ c wait after, q.current.status = .running c ∧
    c.frame.completed = none ∧ c.frame.unwinding = none ∧
    c.frame.waiting = some wait ∧ PV_THR2_Catch316Segment.select c = none ∧
    (match wait.request with | .child fn _ _ => m.programs fn = none | _ => True) ∧
    (step m q).current.status = .running after ∧
    after.frame.activation = c.frame.activation ∧ after.frame.completed = none ∧
    after.frame.waiting = some wait
/-- Client panic strategy is abort. Erase state also at the internal panic
signal; its next administration has exactly the same event prefix. -/
def Aborts (q : State) : Prop :=
  (∃ s, q.current.status = .fault .abort s) ∨
  ∃ s, q.current.status = .fault .panic s

def observe (q : State) : PV_LIB_SPEC_ThreadContract.Observation :=
  match q.current.status with
  | .fault .abort _ | .fault .panic _ => .abort q.current.events
  | _ => PV_LIB_SPEC_D984.observe q

def Boundary (m : Machine) (entry : State) (trace : Nat → State) (n : Nat) : Prop :=
  OwnComplete entry (trace n) ∨ Terminal entry (trace n) ∨
    ∃ k, n = k+1 ∧ Pending m (trace k) ∧ trace n = step m (trace k)
def First (m : Machine) (entry : State) (trace : Nat → State) (n : Nat) : Prop :=
  Boundary m entry trace n ∧ ∀ k, k < n → ¬ Boundary m entry trace k

def Behavior (m : Machine) (entry : State) (candidate : Nat → State) : Prop :=
  let ref := fun n => run m n entry
  (∃ n k, First m entry ref n ∧ First m entry candidate k ∧
    observe (candidate k) = observe (ref n)) ∨
  ((∀ n, ¬ Boundary m entry ref n) ∧ (∀ k, ¬ Boundary m entry candidate k) ∧
    (∀ n, ∃ k, (ref n).current.events = (candidate k).current.events) ∧
    (∀ k, ∃ n, (ref n).current.events = (candidate k).current.events))

/-- Final common own-row Post. This supersedes only the pending recognizer
and panic observation in the earlier compiled Full drafts, not their source
body, domain, representation, resource or frame content. -/
def Post (table : FullStoreActionTable) (r : Runtime)
    (body : PV_STX2_SliceSyntax.Program) (i : Input) (candidate : Nat → State) : Prop :=
  let m := PV_LIB_SPEC_Full.source table r
  Behavior m (entry body i) candidate ∧
  ∀ k, (∀ j, j < k → ¬ Boundary m (entry body i) candidate j) →
    ¬ Aborts (candidate k) → PV_LIB_SPEC_ThreadRow.Frame r i (candidate k)
/-- Explicit old/new frontier comparison target; not presumed an equivalence
at a resource override, where the fallback answer may differ. -/
def Comparison (m : Machine) (q : State) : Prop :=
  PV_LIB_SPEC_D984.ConsumedPending m q → Pending m q

#print axioms Pending
#print axioms Aborts
#print axioms observe
#print axioms Boundary
#print axioms First
#print axioms Behavior
#print axioms Post
#print axioms Comparison
end PV_LIB_SPEC_Frontier

namespace PV_LIB_SPEC_OwnInitFull
open Aeneas Aeneas.Std PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_F0Full.Original
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec
abbrev Pre := PV_LIB_SPEC_F0Full.PreRoot
abbrev entry := PV_LIB_SPEC_F0Full.rootEntry
/-- Source/binary parameters fixed before execution, never a receiver, payload
or successful decoder chosen to fit a later state. -/
structure Representation where
  loadBias : PV_OWN2_Codec.Pointer
  siteIndex : Fin 11
  granted : PV_OWN2_FreshAllocation.GrantedRegions

def InitPoll (q : State) : Prop :=
  ∃ c wait a payload, q.current.status = .running c ∧
    c.frame.completed = none ∧ c.frame.waiting = some wait ∧
    PV_THR2_OwnInitAction.selected c = true ∧
    wait.request = .child PV_THR2_Source361InitChildren.fnAllocationFull a [payload]

/-- The allocation/store milestone is AFTER the actual14756 reply, including
failure, null/abort, divergence or pending. Earlier stops retain their actual
source frontier; a no-spawn path may reach the original function completion. -/
def Boundary (m : Machine) (i : Input) (trace : Nat → State) (n : Nat) : Prop :=
  PV_LIB_SPEC_Frontier.Boundary m (entry i) trace n ∨
    ∃ k, n = k+1 ∧ InitPoll (trace k) ∧ trace n = step m (trace k)
def First (m : Machine) (i : Input) (trace : Nat → State) (n : Nat) : Prop :=
  Boundary m i trace n ∧ ∀ k, k < n → ¬ Boundary m i trace k

/-- SAME-history ownership conclusion. All callback allocation,14320
registration,14756 payload/bridge and post-store associations are conclusions
inside this witness, never original-entry or callee-success premises. -/
def AllocationWitness (table : FullStoreActionTable) (r : Runtime)
    (R : Representation) (i : Input) (trace : Nat → State) (n : Nat) : Prop :=
  ∃ (callbackIndex registrationIndex readyIndex pollIndex : Nat)
    (callback registration ready poll : Config)
    (wait : PV_STX2_Native.Waiting Data) (requestActivation : Nat)
    (handle data : PV_OWN2_Codec.Pointer) (backend : PV_STX_World.World),
    callbackIndex < registrationIndex ∧ registrationIndex < readyIndex ∧
    readyIndex+1 = pollIndex ∧ n = pollIndex+1 ∧
    (trace callbackIndex).current.status = .running callback ∧
    callback.frame.remaining = PV_THR2_F361.live.body.drop 94 ∧
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

/-- There is NO Some premise. Some/allocation is the witness branch; no-box
completion and every earlier stop compare to the same independent reference.
Infinite execution retains every finite observable prefix and no finite return. -/
def Post (table : FullStoreActionTable) (r : Runtime) (R : Representation)
    (i : Input) (candidate : Nat → State) : Prop :=
  let m := PV_LIB_SPEC_Full.source table r
  let ref := fun n => run m n (entry i)
  ((∃ n k, First m i ref n ∧ First m i candidate k ∧
      PV_LIB_SPEC_Frontier.observe (candidate k) = PV_LIB_SPEC_Frontier.observe (ref n) ∧
      ((∃ before, n = before+1 ∧ InitPoll (ref before)) →
        AllocationWitness table r R i ref n)) ∨
    ((∀ n, ¬ Boundary m i ref n) ∧ (∀ k, ¬ Boundary m i candidate k) ∧
      (∀ n, ∃ k, (ref n).current.events = (candidate k).current.events) ∧
      (∀ k, ∃ n, (ref n).current.events = (candidate k).current.events))) ∧
  ∀ k, (∀ j, j < k → ¬ Boundary m i candidate j) →
    ¬ PV_LIB_SPEC_Frontier.Aborts (candidate k) →
      PV_LIB_SPEC_F0Full.RootFrame r i (candidate k)

def Contract (table : FullStoreActionTable) (r : Runtime) (R : Representation)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r R i (implementation m i)
/-- These exact existing exports are named consumers for the composition
proof. Aliasing their TYPES/terms is not application at an actual14756 run. -/
abbrev AllocationExport := @PV_THR2_OwnInitActualAllocationOwned.allBridged
abbrev OwnershipExport := @PV_OWN2_Exports.SourceInitBoxOwnership
/-- Original ledger draft's extra Some condition, preserved for comparison
only. The new Pre contains no such condition. This formula is NOT assumed. -/
def LegacySome (table : FullStoreActionTable) (r : Runtime) (i : Input) : Prop :=
  ∃ n, InitPoll (run (PV_LIB_SPEC_Full.source table r) n (entry i))
def Comparison (table : FullStoreActionTable) (r : Runtime) (R : Representation)
    (implementation : Machine → Input → Nat → State) : Prop :=
  (∀ i, (Pre r i ∧ LegacySome table r i) → Pre r i) ∧
  Contract table r R implementation

#print axioms MachineSpec
#print axioms Pre
#print axioms Representation
#print axioms InitPoll
#print axioms Boundary
#print axioms First
#print axioms AllocationWitness
#print axioms Post
#print axioms Contract
#print axioms AllocationExport
#print axioms OwnershipExport
#print axioms LegacySome
#print axioms Comparison
end PV_LIB_SPEC_OwnInitFull
