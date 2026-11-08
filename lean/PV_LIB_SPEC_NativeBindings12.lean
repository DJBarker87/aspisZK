import PV_LIB_SPEC_CallbackModel
import PV_LIB_SPEC_NativeBoolRuntime
import PV_LIB_SPEC_ThreadNewNative
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_NativeBindings12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
local instance : DecidableEq Data := Classical.decEq _

/-- The exact generic Arc BoxNew token. Callback BoxNew is a different
monomorphization and stays on its source-derived byte-store branch. -/
def isArc (request : PV_STX2_Native.Request Data) : Bool :=
  match request with
  | .child fn _ _ => decide (fn=PV_THR2_Packet124BoxIssue17.fn)
  | _ => false

/-- Constructors and the absent-name native Thread allocation are installed
at the actual request. Source projections may fail explicitly; no successful
projection is a machine premise. Other-name213 remains the historical native
branch and earns no new adequate-name credit. -/
def core (rsp : Nat) (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) :=
  if isArc request then PV_LIB_SPEC_NativeBoolRuntime.answer p c request w
  else if PV_LIB_SPEC_NativeConstructors.selected request then
    PV_LIB_SPEC_NativeConstructors.reply request w
      (PV_THR2_OwnUniformResourceHandler.lift p.environment.native request w)
  else match request with
  | .child fn _ args =>
    if PV_THR2_OffPath.functionId fn = some 213 then
      match args with
      | [_,label] =>
        if (runtime p).control.variant label = some 0 then do
          let (id,length) ← PV_LIB_SPEC_ThreadNewNative.operands p c w args
          PV_LIB_SPEC_ThreadNewNative.reply p c request w id length
        else PV_LIB_SPEC_NativeModel.answer rsp p c request w
      | _ => none
    else PV_LIB_SPEC_NativeModel.answer rsp p c request w
  | _ => PV_LIB_SPEC_NativeModel.answer rsp p c request w

def answer (rsp : Nat) (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) :=
  (core rsp p c request w).map (PV_LIB_SPEC_BoundRuntime.frameReply request w)

def handler (rsp : Nat) (p : Parameters) (c : Config) : Handler :=
  fun request w => (answer rsp p c request w).getD
    (PV_THR2_OwnUniformResourceHandler.lift p.environment.native request w)

theorem ordinary_framed (rsp : Nat) (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) (r : Reply OWNER Event Data)
    (ordinary : PV_LIB_SPEC_BoundRuntime.allocationToken request = false)
    (result : answer rsp p c request w = some r) :
    PV_LIB_SPEC_NativeRuntime.GhostFrame w r.world := by
  unfold answer at result
  cases h : core rsp p c request w with
  | none => rw [h] at result; cases result
  | some raw =>
    rw [h] at result
    cases result
    exact PV_LIB_SPEC_BoundRuntime.ordinary_framed request w raw ordinary

#print axioms isArc
#print axioms answer
#print axioms handler
#print axioms ordinary_framed
#print axioms core
/-- Same latest lane-A v2 definitions, privately replayed with import-only
renames against W3. This parameter is the existing VALUE-only interface;
no replacement table, Store transformer or write-definedness law is accepted.
Its concrete source binding is still required before a full witness claim. -/
def transition (rsp : Nat) (values : PV_THR2_SourceStoreLibrary.Values OWNER Event)
    (p : Parameters) (c : Config) (q : State) : State :=
  PV_LIB_StoreActionTable.step (runtime p).carrier (runtime p).control
    PV_LIB_SPEC_Full.programs p.resources p.encode
    (handler rsp p c) values q

def control (rsp : Nat) (values : PV_THR2_SourceStoreLibrary.Values OWNER Event)
    (p : Parameters) (q : State) : State :=
  match q.current.status with
  | .running c => transition rsp values p c q
  | _ => transition rsp values p ⟨{activation := 0,remaining := []},[],⟨fun _ => none,0⟩⟩ q

/-- Callback byte-store native assembly, with scalar registers derived from source and explicit native rsp, with the ACTUAL v2 step. Every resource
context is obtained from the actual issued history; no table parameter remains. -/
def step (rsp : Nat) (values : PV_THR2_SourceStoreLibrary.Values OWNER Event)
    (p : Parameters) (x : Execution) : Execution :=
  match PV_LIB_SPEC_ControlRuntime.ordinary x.state with
  | none =>
    let out := control rsp values p x.state
    {x with state := out,issued := PV_LIB_SPEC_ControlRuntime.recordIssue x.state out x.issued}
  | some (c,wait) =>
    match context x c wait with
    | none => {x with state :=
        ⟨⟨.undefined none c.store,x.state.current.world,x.state.current.events⟩,x.state.suspended⟩}
    | some ctx =>
      let bound := {p with resources := allocationResources p.environment ctx}
      match answer rsp bound c wait.request x.state.current.world with
      | none =>
        let r := PV_THR2_OwnUniformResourceHandler.lift p.environment.native wait.request x.state.current.world
        {x with
          state := ⟨⟨.undefined none c.store,r.world,x.state.current.events ++ r.events⟩,x.state.suspended⟩
          consumed := ctx :: x.consumed}
      | some _ =>
        let out := transition rsp values bound c x.state
        {state := out,issued := PV_LIB_SPEC_ControlRuntime.recordIssue x.state out x.issued,consumed := ctx :: x.consumed}

def run (rsp : Nat) (values : PV_THR2_SourceStoreLibrary.Values OWNER Event) (p : Parameters) : Nat → Execution → Execution
  | 0,x => x
  | n+1,x => run rsp values p n (step rsp values p x)

abbrev actions := PV_LIB_StoreActionTable.v2

theorem preserves_owner_away (rsp : Nat) (values : PV_THR2_SourceStoreLibrary.Values OWNER Event)
    (p : Parameters) (c : Config) (q : State)
    (away : PV_LIB_StoreActionTable.Neutral PV_LIB_SPEC_Full.programs q) :
    transition rsp values p c q =
      PV_THR2_OwnInitInterpreterBridged.step (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs p.resources p.encode (handler rsp p c) q :=
  PV_LIB_StoreActionTable.agreement _ _ _ _ _ _ _ _ away

#print axioms transition
#print axioms control
#print axioms step
#print axioms run
#print axioms actions
#print axioms preserves_owner_away
end PV_LIB_SPEC_NativeBindings12
