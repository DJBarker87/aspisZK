import PV_LIB_SPEC_PreludeValues14
import PV_LIB_SPEC_ScopePhysical13
import PV_LIB_SPEC_Builder269
import PV_LIB_SPEC_CellPhysical13
import PV_LIB_SPEC_ThreadId13
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Assembly14
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory
local instance : DecidableEq Data := Classical.decEq _

abbrev Cut := PV_LIB_SPEC_PrefixNative14.Cut

def core (cut : Cut) (p : Parameters) (c : Config)
    (request : PV_STX2_Native.Request Data) (w : OWNER) : Option (Reply OWNER Event Data) :=
  match request with
  | .child fn _ args =>
    if fn=PV_LIB_SPEC_PreludeValues14.fn164 then
      PV_LIB_SPEC_PreludeValues14.reply p c w 164 args
        (PV_THR2_OwnUniformResourceHandler.lift p.environment.native request w)
    else if fn=PV_LIB_SPEC_PreludeValues14.fn165 then
      PV_LIB_SPEC_PreludeValues14.reply p c w 165 args
        (PV_THR2_OwnUniformResourceHandler.lift p.environment.native request w)
    else if fn=PV_LIB_SPEC_PreludeValues14.fn93 then
      PV_LIB_SPEC_PreludeValues14.reply p c w 93 args
        (PV_THR2_OwnUniformResourceHandler.lift p.environment.native request w)
    else PV_LIB_SPEC_PrefixNative14.answer cut p c request w
  | _ => PV_LIB_SPEC_PrefixNative14.answer cut p c request w

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
/-- Actual retained v2, with the concrete partial Values14 instance.
Growth adequacy and full-table coverage are still open. -/
def transition (cut : Cut) (p : Parameters) (c : Config) (q : State) : State :=
  PV_LIB_StoreActionTable.step (runtime p).carrier (runtime p).control
    PV_LIB_SPEC_Full.programs p.resources p.encode
    (handler cut p c) (PV_LIB_SPEC_Values14.values p) q

def control (cut : Cut) (p : Parameters) (q : State) : State :=
  match q.current.status with
  | .running c => transition cut p c q
  | _ => transition cut p ⟨{activation := 0,remaining := []},[],⟨fun _ => none,0⟩⟩ q

/-- Callback byte-store native assembly, with scalar registers derived from source and explicit native rsp, with the ACTUAL v2 step. Every resource
context is obtained from the actual issued history; no table parameter remains. -/
def step (cut : Cut) (p : Parameters) (x : Execution) : Execution :=
  match PV_LIB_SPEC_ControlRuntime.ordinary x.state with
  | none =>
    let out := control cut p x.state
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
        let out := transition cut bound c x.state
        {state := out,issued := PV_LIB_SPEC_ControlRuntime.recordIssue x.state out x.issued,consumed := ctx :: x.consumed}

def run (cut : Cut) (p : Parameters) : Nat → Execution → Execution
  | 0,x => x
  | n+1,x => run cut p n (step cut p x)

abbrev actions := PV_LIB_StoreActionTable.v2

theorem preserves_owner_away (cut : Cut) (p : Parameters) (c : Config) (q : State)
    (away : PV_LIB_StoreActionTable.Neutral PV_LIB_SPEC_Full.programs q) :
    transition cut p c q =
      PV_THR2_OwnInitInterpreterBridged.step (runtime p).carrier (runtime p).control
        PV_LIB_SPEC_Full.programs p.resources p.encode (handler cut p c) q :=
  PV_LIB_StoreActionTable.agreement _ _ _ _ _ _ _ _ away

#print axioms transition
#print axioms control
#print axioms step
#print axioms run
#print axioms actions
#print axioms preserves_owner_away
end PV_LIB_SPEC_Assembly14
