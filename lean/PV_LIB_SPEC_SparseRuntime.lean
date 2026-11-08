import PV_LIB_SPEC_SparsePacketHandler
import PV_LIB_SPEC_ControlRuntime
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_SparseRuntime
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984
open PV_LIB_SPEC_Frozen PV_LIB_SPEC_ResourceHistory
def pureValue (C : Carrier OWNER Data) (K : Control) (w : OWNER)
    (fn : Data) (args : List Data) : Option Data := do
  match PV_THR2_OffPath.functionId fn,args with
  | some 121,[.number n] =>
    some (PV_FN_THREAD_f360Outcomes.atomicValue PV_LIB_SPEC_FrozenABI.atomicKind PV_LIB_SPEC_FrozenABI.unsafeCellKind n)
  | some 277,[arg] =>
    match C.dereference w arg with
    | some p => some (PV_FN_THREAD_f170.SourceTlsValue.optionSome PV_LIB_SPEC_FrozenABI.optionType p).encode
    | none => some (PV_FN_THREAD_f170.SourceTlsValue.optionNone PV_LIB_SPEC_FrozenABI.optionType).encode
  | some 278,[arg,_] =>
    match K.variant arg,C.field arg 0 with
    | some 0,_ => some (PV_FN_THREAD_f170.SourceTlsValue.resultErr PV_LIB_SPEC_FrozenABI.resultType).encode
    | some 1,some value =>
      let p ← C.dereference w value
      some (PV_FN_THREAD_f170.SourceTlsValue.resultOk PV_LIB_SPEC_FrozenABI.resultType p).encode
    | _,_ => none
  | some 279,[arg] =>
    match K.variant arg,C.field arg 0 with
    | some 1,_ => some (PV_FN_THREAD_f170.SourceTlsValue.controlBreak PV_LIB_SPEC_FrozenABI.flowType PV_LIB_SPEC_FrozenABI.residualType).encode
    | some 0,some value =>
      let p ← C.dereference w value
      some (PV_FN_THREAD_f170.SourceTlsValue.controlContinue PV_LIB_SPEC_FrozenABI.flowType p).encode
    | _,_ => none
  | _,_ => none

/-- Retain every nonsuccess answer. Pure TLS leaves frame the world on EVERY
answer (D935); AtomicUsize::new frames it on returned success (D898).
The step below marks malformed returned pure values undefined. -/
def values (C : Carrier OWNER Data) (K : Control) (H : Handler) : Handler :=
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
          match pureValue C K w fn args with
          | some v => ⟨.returned (.ok v),w,r.events⟩
          | none => ⟨r.answer,pureWorld,r.events⟩
        | _ => ⟨r.answer,pureWorld,r.events⟩
      | _ => r
    | _ => r


/-- ABI metadata and48/8 sparse Packet image are fixed, with no ABI/Shape
parameter. All existing named pointer, callback and bridged box models remain.
The partial Packet codec exposes invalid source association as None. -/
def native (p : Parameters) (c : Config) (request : PV_STX2_Native.Request Data)
    (w : OWNER) : Option (Reply OWNER Event Data) :=
  let C := (runtime p).carrier
  let K := (runtime p).control
  let H := PV_THR2_FnOnceDispatch.handler
    (values C K (PV_THR2_OwnUniformResourceHandler.lift p.environment.native))
  let H := PV_THR2_ManuallyDropHandler.handler H
  let H := PV_THR2_IntrinsicSemantics_NonNullAsRef.handler C c.store H
  let H := PV_THR2_PacketPointerSemantics.handler H
  let H := PV_THR2_ClosureBoxActivationHandler.handler p.resources p.encode H
  match request with
  | .child _ a _ => PV_LIB_SPEC_SparsePacketHandler.handler C K p.resources p.encode
      {c.store with nextActivation := a} H request w
  | _ => some (H request w)

def invalidPure (p : Parameters) (c : Config) (w : OWNER) : Bool :=
  match c.frame.waiting with
  | some wait => match wait.request with
    | .child fn _ args =>
      match PV_THR2_OffPath.functionId fn with
      | some 121 | some 277 | some 278 | some 279 =>
        match (PV_THR2_OwnUniformResourceHandler.lift p.environment.native wait.request w).answer with
        | .returned (.ok _) => (pureValue (runtime p).carrier (runtime p).control w fn args).isNone
        | _ => false
      | _ => false
    | _ => false
  | none => false

/-- Rechecked BoundRuntime value/ghost assembly. Every ordinary full answer
is framed, including failure/pending; only exact named allocation tokens may
change registry fields. Arc returned value uses the actual reached count. -/
def valueAnswer (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) := do
  let r ← native p c request w
  let r ← match request with
    | .child fn _ args =>
      if PV_THR2_OffPath.functionId fn = some 360 then
        match r.answer with
        | .returned (.ok _) => do
          let (value,count) ← PV_LIB_SPEC_BoundRuntime.arc (runtime p).carrier c.store w args
          if count > PV_THR2_LibrarySemantics_ArcClone.maxRefcount then
            some ⟨.fault .abort,w,r.events⟩
          else some ⟨.returned (.ok value),w,r.events⟩
        | _ => some r
      else if invalidPure p c w then none else some r
    | _ => some r
  pure r

def answer (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) :=
  (valueAnswer p c request w).map (PV_LIB_SPEC_BoundRuntime.frameReply request w)

def handler (p : Parameters) (c : Config) : Handler :=
  fun request w => (answer p c request w).getD
    (PV_THR2_OwnUniformResourceHandler.lift p.environment.native request w)

def machineAt (table : FullStoreActionTable) (p : Parameters) (c : Config) : Machine :=
  {source table p with handler := handler p c}

def controlStep (table : FullStoreActionTable) (p : Parameters) (q : State) : State :=
  match q.current.status with
  | .running c => PV_LIB_SPEC_D984.step (machineAt table p c) q
  | _ => PV_LIB_SPEC_D984.step (source table p) q

/-- Fresh lane-owned runtime; the total-image runtime is retained as historical
model evidence only. Resources are selected from the actual issued origin.
No writer semantics, resource success or codec success is assumed here. -/
def step (table : FullStoreActionTable) (p : Parameters) (x : Execution) : Execution :=
  match PV_LIB_SPEC_ControlRuntime.ordinary x.state with
  | none =>
    let out := controlStep table p x.state
    {x with state := out,issued := PV_LIB_SPEC_ControlRuntime.recordIssue x.state out x.issued}
  | some (c,wait) =>
    match context x c wait with
    | none => {x with state :=
        ⟨⟨.undefined none c.store,x.state.current.world,x.state.current.events⟩,x.state.suspended⟩}
    | some ctx =>
      let bound := {p with resources := allocationResources p.environment ctx}
      match answer bound c wait.request x.state.current.world with
      | none =>
        let r := PV_THR2_OwnUniformResourceHandler.lift p.environment.native wait.request x.state.current.world
        {x with
          state := ⟨⟨.undefined none c.store,r.world,x.state.current.events ++ r.events⟩,x.state.suspended⟩
          consumed := ctx :: x.consumed}
      | some _ =>
        let out := PV_LIB_SPEC_D984.step (machineAt table bound c) x.state
        {state := out,issued := PV_LIB_SPEC_ControlRuntime.recordIssue x.state out x.issued,consumed := ctx :: x.consumed}

def run (table : FullStoreActionTable) (p : Parameters) : Nat → Execution → Execution
  | 0,x => x
  | n+1,x => run table p n (step table p x)

/-- The ghost frame is independent of any byte image, and is rechecked against
the sparse assembly on every answer. Named allocations are the only exceptions. -/
theorem ordinary_framed (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) (r : Reply OWNER Event Data)
    (ordinary : PV_LIB_SPEC_BoundRuntime.allocationToken request = false)
    (result : answer p c request w = some r) :
    PV_LIB_SPEC_NativeRuntime.GhostFrame w r.world := by
  unfold answer at result
  cases hv : valueAnswer p c request w with
  | none => rw [hv] at result; cases result
  | some original =>
    rw [hv] at result
    cases result
    exact PV_LIB_SPEC_BoundRuntime.ordinary_framed request w original ordinary

#print axioms pureValue
#print axioms values
#print axioms native
#print axioms invalidPure
#print axioms valueAnswer
#print axioms answer
#print axioms handler
#print axioms machineAt
#print axioms controlStep
#print axioms step
#print axioms run
#print axioms ordinary_framed
end PV_LIB_SPEC_SparseRuntime
