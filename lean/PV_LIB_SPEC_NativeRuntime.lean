import PV_LIB_SPEC_OwnInitComposition
import PV_THR2_PacketJoinedHandler
import PV_THR2_ClosureBoxActivationHandler
import PV_THR2_ManuallyDropHandler
import PV_THR2_LibrarySemantics_TLSSourceValues
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_NativeRuntime
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984
/-- ABI metadata is fixed before the run. ArcInner is the provider's named
layout/image interface; TLS result type descriptors are source metadata, not
successful decoder hypotheses or a function selecting a desired write. -/
structure ABI where
  arcInner : PV_THR2_TypedRepresentation_ArcInner.Shape
  atomicKind : Data
  unsafeCellKind : Data
  optionType : Data
  resultType : Data
  flowType : Data
  residualType : Data

/-- Pure source values. None is an interpretation gap, never an arbitrary
successful result. The pointer comes from the actual argument, at this world. -/
def pureValue (abi : ABI) (C : Carrier OWNER Data) (K : Control) (w : OWNER)
    (fn : Data) (args : List Data) : Option Data := do
  match PV_THR2_OffPath.functionId fn,args with
  | some 121,[.number n] =>
    some (PV_FN_THREAD_f360Outcomes.atomicValue abi.atomicKind abi.unsafeCellKind n)
  | some 277,[arg] =>
    match C.dereference w arg with
    | some p => some (PV_FN_THREAD_f170.SourceTlsValue.optionSome abi.optionType p).encode
    | none => some (PV_FN_THREAD_f170.SourceTlsValue.optionNone abi.optionType).encode
  | some 278,[arg,_] =>
    match K.variant arg,C.field arg 0 with
    | some 0,_ => some (PV_FN_THREAD_f170.SourceTlsValue.resultErr abi.resultType).encode
    | some 1,some value =>
      let p ← C.dereference w value
      some (PV_FN_THREAD_f170.SourceTlsValue.resultOk abi.resultType p).encode
    | _,_ => none
  | some 279,[arg] =>
    match K.variant arg,C.field arg 0 with
    | some 1,_ => some (PV_FN_THREAD_f170.SourceTlsValue.controlBreak abi.flowType abi.residualType).encode
    | some 0,some value =>
      let p ← C.dereference w value
      some (PV_FN_THREAD_f170.SourceTlsValue.controlContinue abi.flowType p).encode
    | _,_ => none
  | _,_ => none

/-- Retain every nonsuccess answer. Pure TLS leaves frame the world on EVERY
answer (D935); AtomicUsize::new frames it on returned success (D898).
The step below marks malformed returned pure values undefined. -/
def values (abi : ABI) (C : Carrier OWNER Data) (K : Control) (H : Handler) : Handler :=
  fun request w =>
    let r := H request w
    match request with
    | .child fn _ args =>
      match PV_THR2_OffPath.functionId fn with
      | some 121 | some 277 | some 278 | some 279 =>
        let pureWorld := match PV_THR2_OffPath.functionId fn with
          | some 121 => r.world | _ => w
        match r.answer with
        | .returned (.ok _) =>
          match pureValue abi C K w fn args with
          | some v => ⟨.returned (.ok v),w,r.events⟩
          | none => ⟨r.answer,pureWorld,r.events⟩
        | _ => ⟨r.answer,pureWorld,r.events⟩
      | _ => r
    | _ => r

/-- Only named allocation/OWNER handlers are outside the framed backend lift.
Use the reached source store for dereference. Box backing uses the ACTUALLY
issued activation; the counter projection is local administration, not an
interface requiring equality of callee counters (D961). -/
def native (p : PV_LIB_SPEC_Frozen.Parameters) (abi : ABI) (c : Config) : Handler :=
  fun request w =>
    let C := (PV_LIB_SPEC_Frozen.runtime p).carrier
    let H := PV_THR2_FnOnceDispatch.handler
      (values abi C (PV_LIB_SPEC_Frozen.runtime p).control (PV_THR2_OwnUniformResourceHandler.lift p.environment.native))
    let H := PV_THR2_ManuallyDropHandler.handler H
    let H := PV_THR2_IntrinsicSemantics_NonNullAsRef.handler C c.store H
    let H := PV_THR2_PacketPointerSemantics.handler H
    let H := PV_THR2_ClosureBoxActivationHandler.handler p.resources p.encode H
    match request with
    | .child _ a _ =>
      PV_THR2_PacketBoxImageHandler.handler p.resources p.encode
        {c.store with nextActivation := a} abi.arcInner H request w
    | _ => H request w

def invalidPure (p : PV_LIB_SPEC_Frozen.Parameters) (abi : ABI)
    (c : Config) (w : OWNER) : Bool :=
  match c.frame.waiting with
  | some wait => match wait.request with
    | .child fn _ args =>
      match PV_THR2_OffPath.functionId fn with
      | some 121 | some 277 | some 278 | some 279 =>
        match (PV_THR2_OwnUniformResourceHandler.lift p.environment.native wait.request w).answer with
        | .returned (.ok _) => (pureValue abi (PV_LIB_SPEC_Frozen.runtime p).carrier
            (PV_LIB_SPEC_Frozen.runtime p).control w fn args).isNone
        | _ => false
      | _ => false
    | _ => false
  | none => false

/-- New reference step. The frozen18 source statements remain historical;
new statements must use this reached-context native assembly. The completed
lane-A table remains independent and explicit. The OWNER-aware base retains
its exact14320 registration, operator actions and bridged14756 handler. -/
def machineAt (table : FullStoreActionTable) (p : PV_LIB_SPEC_Frozen.Parameters)
    (abi : ABI) (c : Config) : Machine :=
  {PV_LIB_SPEC_Frozen.source table p with handler := native p abi c}

def step (table : FullStoreActionTable) (p : PV_LIB_SPEC_Frozen.Parameters)
    (abi : ABI) (q : State) : State :=
  match q.current.status with
  | .running c =>
    if invalidPure p abi c q.current.world then
      let wait := c.frame.waiting
      let r := match wait with
        | some wait => native p abi c wait.request q.current.world
        | none => ⟨.pending,q.current.world,[]⟩
      ⟨⟨.undefined none c.store,r.world,q.current.events ++ r.events⟩,q.suspended⟩
    else PV_LIB_SPEC_D984.step (machineAt table p abi c) q
  | _ => PV_LIB_SPEC_D984.step (PV_LIB_SPEC_Frozen.source table p) q

/-- Exact named action envelope, an audit target rather than an assumption:
ordinary native fallback cannot mutate OWNER ghost state; named allocation
handlers above and OWNER-aware administrative actions alone can do so. -/
def GhostFrame (before after : OWNER) : Prop :=
  after.next = before.next ∧ after.places = before.places ∧
    after.world.frame = before.world.frame

theorem backend_framed (p : PV_LIB_SPEC_Frozen.Parameters)
    (request : PV_STX2_Native.Request Data) (w : OWNER) :
    GhostFrame w (PV_THR2_OwnUniformResourceHandler.lift p.environment.native request w).world :=
  ⟨rfl,rfl,rfl⟩

#print axioms ABI
#print axioms pureValue
#print axioms values
#print axioms native
#print axioms invalidPure
#print axioms machineAt
#print axioms step
#print axioms GhostFrame
#print axioms backend_framed
end PV_LIB_SPEC_NativeRuntime
