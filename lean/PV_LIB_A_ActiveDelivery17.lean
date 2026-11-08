import PV_LIB_A_ActiveTlsNative17
import PV_LIB_SPEC_NativeDelivery16
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActiveDelivery17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)

/-- The context is computed from the most recent emitted origin, retaining
all earlier issues/consumption. No external occurrence or resource index. -/
local instance : DecidableEq Site := Classical.decEq _

def origin (site : Site) (caller : Nat) (request : PV_STX2_Native.Request Data)
    (consumed : List Context) : Context :=
  ⟨site,(consumed.filter (fun old => decide (old.site=site))).length,
    PV_LIB_SPEC_ResourceHistory.arguments request,caller,request⟩

/-- Uniform native consumption lemma. Each actual use discharges lookup,
source-store neutrality and the COMPLETE native answer by named contracts. -/
theorem consume (cut : PV_LIB_SPEC_ReachedNative14.Cut)
    (c : Config) (wait : PV_STX2_Native.Waiting Data) (site : Site)
    (w : OWNER) (events : List Event) (issued : List Issued) (consumed : List Context)
    (fn : Data) (a dest : Nat) (args : List Data) (r : Reply OWNER Event Data)
    (quiet : PV_LIB_SPEC_SourceTransport15.Quiet ⟨⟨.running c,w,events⟩,[]⟩)
    (intrinsic : PV_THR2_Catch316Segment.select c = none)
    (action : wait.action = .child a (.local dest))
    (done : c.frame.completed = none) (unwind : c.frame.unwinding = none)
    (saved : c.frame.waiting = some wait) (requested : wait.request = .child fn a args)
    (lookup : PV_LIB_SPEC_Full.programs fn = none)
    (answer : ∀ resources, PV_LIB_SPEC_ReachedNative14.answer cut
      (PV_LIB_SPEC_TlsBound15.parameters resources) c wait.request w = some r) :
    let x : Execution := ⟨⟨⟨.running c,w,events⟩,[]⟩,
      ⟨site,c.frame.activation,wait.request⟩::issued,consumed⟩
    let out := PV_THR2_ChildBoundary.delivered (runtime PV_LIB_SPEC_ReachedEnvironment14.parameters).carrier c wait r
    PV_LIB_SPEC_ReachedNative14.step cut PV_LIB_SPEC_ReachedEnvironment14.parameters x =
      ⟨⟨⟨out.status,out.world,events ++ out.events⟩,[]⟩,x.issued,
        origin site c.frame.activation wait.request consumed :: consumed⟩ := by
  dsimp only
  have ordinary : PV_LIB_SPEC_ControlRuntime.ordinary ⟨⟨.running c,w,events⟩,[]⟩ = some (c,wait) := by
    simp [PV_LIB_SPEC_ControlRuntime.ordinary,done,intrinsic,saved,requested,lookup]
  let x : Execution := ⟨⟨⟨.running c,w,events⟩,[]⟩,⟨site,c.frame.activation,wait.request⟩::issued,consumed⟩
  have context : PV_LIB_SPEC_ResourceHistory.context x c wait =
      some (origin site c.frame.activation wait.request consumed) := by
    classical
    simp [PV_LIB_SPEC_ResourceHistory.context,x,origin]
  unfold PV_LIB_SPEC_ReachedNative14.step
  rw [ordinary]
  change (match PV_LIB_SPEC_ResourceHistory.context x c wait with | none => _ | some ctx => _) = _
  rw [context]
  dsimp only
  let resources : Resources := PV_LIB_SPEC_ResourceHistory.allocationResources
    PV_LIB_SPEC_ReachedEnvironment14.parameters.environment (origin site c.frame.activation wait.request consumed)
  have result := answer resources
  dsimp only [PV_LIB_SPEC_TlsBound15.parameters] at result
  rw [result]
  have delivery := PV_LIB_SPEC_NativeDelivery16.full cut (PV_LIB_SPEC_TlsBound15.parameters resources)
    c w events [] wait fn a dest args quiet intrinsic action done saved requested lookup
  have handler : PV_LIB_SPEC_ReachedNative14.handler cut (PV_LIB_SPEC_TlsBound15.parameters resources) c wait.request w = r := by
    simp only [PV_LIB_SPEC_ReachedNative14.handler,answer resources,Option.getD_some]
  rw [handler] at delivery
  dsimp only [PV_LIB_SPEC_TlsBound15.parameters,resources] at delivery
  rw [delivery]
  simp [PV_LIB_SPEC_ControlRuntime.recordIssue,PV_LIB_SPEC_ControlRuntime.issuing,saved]
  exact ⟨rfl,rfl,rfl⟩

#print axioms origin
#print axioms consume
end PV_LIB_A_ActiveDelivery17
