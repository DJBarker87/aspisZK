import PV_LIB_SPEC_Active27820
import PV_LIB_SPEC_LocalReturn20
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace PV_LIB_SPEC_Active27920
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_SPEC_Tls279Values16 (token value)
def argument (address : Address) : Data := PV_LIB_SPEC_Tls278Values15.value address
local instance : DecidableEq Site := Classical.decEq _

def request (s : Store Data) (address : Address) : PV_STX2_Native.Request Data :=
  .child token s.nextActivation [argument address]
def wait (s : Store Data) (address : Address) : PV_STX2_Native.Waiting Data :=
  ⟨request s address,.child s.nextActivation (.local 4),[]⟩
def config (s : Store Data) (a : Nat) (parents : List Frame) (address : Address) : Config :=
  PV_THR2_RunTlsBranchRequest.pending s a parents (argument address)
def origin (s : Store Data) (a : Nat) (address : Address) (consumed : List Context) : Context :=
  ⟨PV_LIB_SPEC_Tls279History16.site,
    (consumed.filter (fun (old : Context) => decide (old.site=PV_LIB_SPEC_Tls279History16.site))).length,
    [argument address],a,request s address⟩
def before (s : Store Data) (a : Nat) (parents : List Frame) (address : Address)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) : Execution :=
  ⟨⟨⟨.running (config s a parents address),w,es⟩,[]⟩,
    ⟨PV_LIB_SPEC_Tls279History16.site,a,request s address⟩ :: issued,consumed⟩
def stored (s : Store Data) (a : Nat) (address : Address) : Store Data :=
  write (write (PV_THR2_RunTlsBranchRequest.issued s a (argument address))
    ⟨s.nextActivation,0,[]⟩ (some (value address))) ⟨a,4,[]⟩ (some (value address))
def out (s : Store Data) (a : Nat) (parents : List Frame) (address : Address)
    (w : OWNER) (es : List Event) : State :=
  ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 24},parents,stored s a address⟩,w,es⟩,[]⟩

theorem ordinary (s : Store Data) (a : Nat) (parents : List Frame) (address : Address)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ControlRuntime.ordinary (before s a parents address w es issued consumed).state =
      some (config s a parents address,wait s address) := by
  have lookup : PV_LIB_SPEC_Full.programs token = none := rfl
  simp [PV_LIB_SPEC_ControlRuntime.ordinary,before,
    config,wait,request,PV_THR2_RunTlsBranchRequest.pending,show PV_THR2_RunTlsBranchRequest.callee=token from rfl,
    PV_THR2_Catch316Segment.select,← show token=PV_THR2_RunTlsBranchRequest.callee from rfl,lookup]

theorem context (s : Store Data) (a : Nat) (parents : List Frame) (address : Address)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) :
    PV_LIB_SPEC_ResourceHistory.context (before s a parents address w es issued consumed)
      (config s a parents address) (wait s address) = some (origin s a address consumed) := by
  classical
  simp [PV_LIB_SPEC_ResourceHistory.context,before,
    config,wait,request,origin,PV_THR2_RunTlsBranchRequest.pending,show PV_THR2_RunTlsBranchRequest.callee=token from rfl,
    PV_LIB_SPEC_ResourceHistory.arguments]

theorem away (s : Store Data) (a : Nat) (parents : List Frame) (address : Address)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) :
    ¬ PV_LIB_A_ActiveEnvironment17.Corrected (before s a parents address w es issued consumed).state := by
  apply PV_LIB_SPEC_ActiveAway20.token _ _ _ (ordinary s a parents address w es issued consumed)
  intro t p eq
  have length := congrArg (fun req => (PV_LIB_SPEC_ResourceHistory.arguments req).length) eq
  change 1=2 at length
  omega

theorem transition (cut : PV_LIB_SPEC_ReachedNative14.Cut) (resources : Resources)
    (s : Store Data) (a : Nat) (parents : List Frame) (address : Address)
    (w : OWNER) (es : List Event) :
    PV_LIB_SPEC_ReachedNative14.transition cut (PV_LIB_SPEC_TlsBound15.parameters resources)
      (config s a parents address) ⟨⟨.running (config s a parents address),w,es⟩,[]⟩ =
      out s a parents address w es := by
  have lookup : PV_LIB_SPEC_Full.programs token = none := rfl
  have table : PV_LIB_StoreActionTable.v2 token = none := rfl
  have quiet : PV_LIB_SPEC_SourceTransport15.Quiet
      ⟨⟨.running (config s a parents address),w,es⟩,[]⟩ := by
    simp [PV_LIB_SPEC_SourceTransport15.Quiet,PV_LIB_StoreActionTable.Neutral,
      PV_LIB_StoreActionTable.select,config,PV_THR2_RunTlsBranchRequest.pending,show PV_THR2_RunTlsBranchRequest.callee=token from rfl,
      PV_THR2_OwnInitAction.selected,PV_THR2_OperatorAction.selected,PV_THR2_OperatorAction.instruction,
      PV_THR2_OwnUniformNeutral.configuration,PV_THR2_OwnUniformNeutral.instruction,
      PV_THR2_F170.live,PV_THR2_F170.block66,PV_THR2_F170.node24,
      ← show token=PV_THR2_RunTlsBranchRequest.callee from rfl,lookup,table]
  rw [PV_LIB_SPEC_NativeDelivery16.full cut _ _ w es [] (wait s address) token s.nextActivation 4
    [argument address] quiet (by rfl) rfl rfl rfl rfl lookup]
  have answer := PV_LIB_SPEC_Tls279Bound16.answer cut resources (config s a parents address)
    w s.nextActivation address (wait s address) rfl rfl
  change PV_LIB_SPEC_ReachedNative14.answer cut (PV_LIB_SPEC_TlsBound15.parameters resources)
    (config s a parents address) (request s address) w = some ⟨.returned (.ok (value address)),w,[]⟩ at answer
  simp only [PV_LIB_SPEC_ReachedNative14.handler,show (wait s address).request=request s address from rfl,
    answer,Option.getD_some]
  simp only [config,PV_THR2_RunTlsBranchRequest.pending,wait,request,
    show PV_THR2_RunTlsBranchRequest.callee=token from rfl]
  rw [PV_LIB_SPEC_LocalReturn20.delivered]
  simp only [out,stored,List.append_nil]

/-- All source facts, actual origin, full computed native reply and consumed
context are derived at the original-issued poll; no desired Store is supplied. -/
theorem consume (cut : PV_LIB_SPEC_ReachedNative14.Cut)
    (s : Store Data) (a : Nat) (parents : List Frame) (address : Address)
    (w : OWNER) (es : List Event) (issued : List Issued) (consumed : List Context) :
    PV_LIB_A_ActiveEnvironment17.step cut PV_LIB_SPEC_ReachedEnvironment14.parameters
      (before s a parents address w es issued consumed) =
      ⟨out s a parents address w es,(before s a parents address w es issued consumed).issued,
        origin s a address consumed :: consumed⟩ := by
  let resources : Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment (origin s a address consumed)
  rw [PV_LIB_SPEC_NativePoll20.consume cut _ _ _ _ _ _ (out s a parents address w es)
    (away s a parents address w es issued consumed)
    (ordinary s a parents address w es issued consumed) (context s a parents address w es issued consumed)
    (PV_LIB_SPEC_Tls279Bound16.answer cut resources _ w s.nextActivation address (wait s address) rfl rfl)
    (transition cut resources s a parents address w es)]
  simp only [before]
  rw [PV_LIB_SPEC_NativePoll20.no_issue _ (wait s address) w es [] _ _ rfl]

#print axioms argument
#print axioms request
#print axioms wait
#print axioms config
#print axioms origin
#print axioms before
#print axioms stored
#print axioms out
#print axioms ordinary
#print axioms context
#print axioms away
#print axioms transition
#print axioms consume
end PV_LIB_SPEC_Active27920
