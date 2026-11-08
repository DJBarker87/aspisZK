import PV_LIB_SPEC_ScopePhysical13
import PV_LIB_SPEC_CellPhysical13
import PV_LIB_SPEC_ThreadId13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_BoundNative13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory

abbrev Cut := PV_LIB_SPEC_Native13.Cut

def core (cut : Cut) (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) :=
  let raw := PV_THR2_OwnUniformResourceHandler.lift p.environment.native request w
  match request with
  | .child fn _ args =>
    match PV_THR2_OffPath.functionId fn with
    | some 360 => PV_LIB_SPEC_ArcPhysical13.reply p c w args raw
    | some 457 => PV_LIB_SPEC_ScopePhysical13.reply p c w args raw
    | some 289 => PV_LIB_SPEC_CellPhysical13.reply cut.active p c w args raw
    | some 371 => PV_LIB_SPEC_CellBindings13.reply p c w fn args raw
    | _ => PV_LIB_SPEC_Native13.answer cut p c request w
  | _ => PV_LIB_SPEC_Native13.answer cut p c request w

def answer (cut : Cut) (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) :=
  (core cut p c request w).map (PV_LIB_SPEC_BoundRuntime.frameReply request w)

def handler (cut : Cut) (p : Parameters) (c : Config) : Handler :=
  fun request w => (answer cut p c request w).getD
    (PV_THR2_OwnUniformResourceHandler.lift p.environment.native request w)

theorem ordinary_framed (cut : Cut) (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) (r : Reply OWNER Event Data)
    (ordinary : PV_LIB_SPEC_BoundRuntime.allocationToken request = false)
    (result : answer cut p c request w = some r) :
    PV_LIB_SPEC_NativeRuntime.GhostFrame w r.world := by
  unfold answer at result
  cases h : core cut p c request w with
  | none => rw [h] at result; cases result
  | some raw =>
    rw [h] at result
    cases result
    exact PV_LIB_SPEC_BoundRuntime.ordinary_framed request w raw ordinary

#print axioms Cut
#print axioms core
#print axioms answer
#print axioms handler
#print axioms ordinary_framed
/-- The actual retained v2 table is unchanged. Values remains its existing
value-only interface; it is not a Store action or a source-adequacy proof. -/
def transition (cut : Cut) (values : PV_THR2_SourceStoreLibrary.Values OWNER Event)
    (p : Parameters) (c : Config) (q : State) : State :=
  PV_LIB_StoreActionTable.step (runtime p).carrier (runtime p).control
    PV_LIB_SPEC_Full.programs p.resources p.encode
    (handler cut p c) values q

def control (cut : Cut) (values : PV_THR2_SourceStoreLibrary.Values OWNER Event)
    (p : Parameters) (q : State) : State :=
  match q.current.status with
  | .running c => transition cut values p c q
  | _ => transition cut values p ⟨{activation := 0,remaining := []},[],⟨fun _ => none,0⟩⟩ q

/-- Callback byte-store native assembly, with scalar registers derived from source and explicit native rsp, with the ACTUAL v2 step. Every resource
context is obtained from the actual issued history; no table parameter remains. -/
def step (cut : Cut) (values : PV_THR2_SourceStoreLibrary.Values OWNER Event)
    (p : Parameters) (x : Execution) : Execution :=
  match PV_LIB_SPEC_ControlRuntime.ordinary x.state with
  | none =>
    let out := control cut values p x.state
    {x with state := out,issued := PV_LIB_SPEC_ControlRuntime.recordIssue x.state out x.issued}
  | some (c,wait) =>
    match context x c wait with
    | none => {x with state :=
        ⟨⟨.undefined none c.store,x.state.current.world,x.state.current.events⟩,x.state.suspended⟩}
    | some ctx =>
      let bound := {p with resources := allocationResources p.environment ctx}
      match answer cut bound c wait.request x.state.current.world with
      | none =>
        let r := PV_THR2_OwnUniformResourceHandler.lift p.environment.native wait.request x.state.current.world
        {x with
          state := ⟨⟨.undefined none c.store,r.world,x.state.current.events ++ r.events⟩,x.state.suspended⟩
          consumed := ctx :: x.consumed}
      | some _ =>
        let out := transition cut values bound c x.state
        {state := out,issued := PV_LIB_SPEC_ControlRuntime.recordIssue x.state out x.issued,consumed := ctx :: x.consumed}

def run (cut : Cut) (values : PV_THR2_SourceStoreLibrary.Values OWNER Event) (p : Parameters) : Nat → Execution → Execution
  | 0,x => x
  | n+1,x => run cut values p n (step cut values p x)

abbrev actions := PV_LIB_StoreActionTable.v2

theorem preserves_owner_away (cut : Cut) (values : PV_THR2_SourceStoreLibrary.Values OWNER Event)
    (p : Parameters) (c : Config) (q : State)
    (away : PV_LIB_StoreActionTable.Neutral PV_LIB_SPEC_Full.programs q) :
    transition cut values p c q =
      PV_THR2_OwnInitInterpreterBridged.step (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs p.resources p.encode (handler cut p c) q :=
  PV_LIB_StoreActionTable.agreement _ _ _ _ _ _ _ _ away

#print axioms transition
#print axioms control
#print axioms step
#print axioms run
#print axioms actions
#print axioms preserves_owner_away
end PV_LIB_SPEC_BoundNative13
