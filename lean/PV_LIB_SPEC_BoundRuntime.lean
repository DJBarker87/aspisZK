import PV_LIB_SPEC_ResourceHistory
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_BoundRuntime
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984
open PV_LIB_SPEC_NativeRuntime PV_LIB_SPEC_Frozen PV_LIB_SPEC_ResourceHistory
local instance : DecidableEq Data := Classical.decEq _

/-- Only these exact native allocation descriptors may change OWNER ghost
fields. 14320 registration and14756 initialization remain named actions of
the OWNER-aware base, outside the ordinary-native channel. -/
def allocationToken (request : PV_STX2_Native.Request Data) : Bool :=
  match request with
  | .child fn _ [_] => decide (fn = PV_THR2_Packet124BoxIssue17.fn ∨
      fn = PV_THR2_Source361BoxTable.fnClosureBoxFull)
  | _ => false

/-- Ordinary replies may change only the backend/heap components exposed by
their named native model. Ghost descriptors are retained on EVERY answer.
The named allocation handlers retain their precise source OWNER updates. -/
def frameReply (request : PV_STX2_Native.Request Data) (w : OWNER)
    (r : Reply OWNER Event Data) : Reply OWNER Event Data :=
  if allocationToken request then r else
    {r with world := {r.world with
      next := w.next
      places := w.places
      world := {r.world.world with frame := w.world.frame}}}

theorem ordinary_framed (request : PV_STX2_Native.Request Data) (w : OWNER)
    (r : Reply OWNER Event Data) (ordinary : allocationToken request = false) :
    GhostFrame w (frameReply request w r).world := by
  simp only [frameReply,ordinary,Bool.false_eq_true,if_false]
  exact ⟨rfl,rfl,rfl⟩

def arc (C : Carrier OWNER Data) (s : Store Data) (w : OWNER)
    (args : List Data) : Option (Data × Nat) := do
  let [arg] := args | none
  let address ← C.dereference w arg
  let value ← readAddress C s address
  let nonNull ← C.field value 0
  let innerPointer ← C.field nonNull 0
  let inner ← C.dereference w innerPointer
  let .number count ← readAddress C s (PV_THR2_LibrarySemantics_ArcClone.countAddress inner) | none
  pure (value,count)

/-- ArcClone's returned value and overflow branch are computed from the
ACTUAL reached store. The independent lane-A action supplies the atomic
source count write; this handler never receives a Store transformer.
Malformed representations return None, never a decoder-success premise. -/
def answer (p : Parameters) (abi : ABI) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) := do
  let r := PV_LIB_SPEC_NativeRuntime.native p abi c request w
  let r ← match request with
    | .child fn _ args =>
      if PV_THR2_OffPath.functionId fn = some 360 then
        match r.answer with
        | .returned (.ok _) => do
          let (value,count) ← arc (runtime p).carrier c.store w args
          if count > PV_THR2_LibrarySemantics_ArcClone.maxRefcount then
            some ⟨.fault .abort,w,r.events⟩
          else some ⟨.returned (.ok value),w,r.events⟩
        | _ => some r
      else if invalidPure p abi c w then none else some r
    | _ => some r
  pure (frameReply request w r)

/-- The selected answer function depends on current source context, never on
an implementation candidate or a future success. Off-request calls are also
interpreted by the same named models; their Option gap is handled at the poll. -/
def handler (p : Parameters) (abi : ABI) (c : Config) : Handler :=
  fun request w => (answer p abi c request w).getD
    (PV_THR2_OwnUniformResourceHandler.lift p.environment.native request w)

/-- Resources are selected from the actual emitted origin BEFORE invoking
any of the three named allocation models. Every ordinary native answer is
framed; invalid value decoding is undefined. BODY/catch/control steps retain
the OWNER-aware base. No desired store, defined write, or successful decoder
is a machine premise. -/
def step (table : FullStoreActionTable) (p : Parameters) (abi : ABI) (x : Execution) : Execution :=
  match ordinary x.state with
  | none =>
    let out := PV_LIB_SPEC_NativeRuntime.step table p abi x.state
    {x with state := out,issued := recordIssue x.state out x.issued}
  | some (c,wait) =>
    match context x c wait with
    | none => {x with state :=
        ⟨⟨.undefined none c.store,x.state.current.world,x.state.current.events⟩,x.state.suspended⟩}
    | some ctx =>
      let bound := {p with resources := allocationResources p.environment ctx}
      match answer bound abi c wait.request x.state.current.world with
      | none =>
        let r := PV_THR2_OwnUniformResourceHandler.lift p.environment.native wait.request x.state.current.world
        {x with
          state := ⟨⟨.undefined none c.store,r.world,x.state.current.events ++ r.events⟩,x.state.suspended⟩
          consumed := ctx :: x.consumed}
      | some _ =>
        let m := {PV_LIB_SPEC_Frozen.source table bound with handler := handler bound abi c}
        let out := PV_LIB_SPEC_D984.step m x.state
        {state := out,issued := recordIssue x.state out x.issued,consumed := ctx :: x.consumed}

def run (table : FullStoreActionTable) (p : Parameters) (abi : ABI) : Nat → Execution → Execution
  | 0,x => x
  | n+1,x => run table p abi n (step table p abi x)

/-- An arbitrary machine satisfying these equations uses the named semantics
at the reached requests. This is an operational specification, not a source
adequacy theorem. Lane A supplies the full table independently. -/
structure Machine where
  transition : Execution → Execution

def source (table : FullStoreActionTable) (p : Parameters) (abi : ABI) : Machine :=
  ⟨step table p abi⟩
def MachineSpec (table : FullStoreActionTable) (p : Parameters) (abi : ABI) (m : Machine) : Prop :=
  m.transition = step table p abi

def execute (m : Machine) : Nat → Execution → Execution
  | 0,x => x
  | n+1,x => execute m n (m.transition x)

#print axioms allocationToken
#print axioms frameReply
#print axioms ordinary_framed
#print axioms arc
#print axioms answer
#print axioms handler
#print axioms step
#print axioms run
#print axioms Machine
#print axioms source
#print axioms MachineSpec
#print axioms execute
end PV_LIB_SPEC_BoundRuntime
