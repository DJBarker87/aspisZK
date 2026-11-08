import PV_LIB_SPEC_ActiveSource19
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ActiveCorrection19
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerHeap PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
open PV_LIB_A_F5CallbackStall16 (config wait)
open PV_LIB_SPEC_TlsNative15 (cut)

/-- SPEC-C18 before: the old exact callback always gives pending. -/
theorem before (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources)
    (s : Store Data) (a : Nat) (parents : List Frame) (pointer : Address) (w : OWNER) :
    PV_LIB_SPEC_ReachedNative14.answer (cut stack)
      (PV_LIB_SPEC_TlsBound15.parameters resources)
      (config s a parents pointer)
      (PV_LIB_A_F5ClosurePending16.request s.nextActivation pointer) w = some ⟨.pending,w,[]⟩ :=
  PV_LIB_A_ActiveDispatch17.before stack resources s a parents pointer w

/-- SPEC-C18 after: exact same source-issued outer callback and context,
computed return/caller frame, source Cell=true and physical byte=1. -/
theorem after_status (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (s : Store Data) (a : Nat)
    (parents : List Frame) (w : OWNER) (es : List Event)
    (issued : List Issued) (consumed : List Context) (ctx : Context)
    (origin : PV_LIB_SPEC_ResourceHistory.context
      ⟨PV_LIB_A_F5CallbackTrap16.waiting s a parents PV_LIB_SPEC_Entry13.slot.source w es,issued,consumed⟩
      (config s a parents PV_LIB_SPEC_Entry13.slot.source)
      (wait s PV_LIB_SPEC_Entry13.slot.source) = some ctx)
    (active : PV_LIB_SPEC_TlsBindings13.read PV_LIB_SPEC_Entry13.slot
      (PV_LIB_SPEC_ActiveConsumption19.bound ctx)
      (config s a parents PV_LIB_SPEC_Entry13.slot.source) w = some false) :
    (PV_LIB_A_ActiveEnvironment17.step (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters
      ⟨PV_LIB_A_F5CallbackTrap16.waiting s a parents PV_LIB_SPEC_Entry13.slot.source w es,issued,consumed⟩).state.current.status =
      .running ⟨{activation := a,remaining := PV_THR2_F170.live.body.drop 40},parents,
        PV_LIB_SPEC_ActiveSource19.store s a parents⟩ := by
  rw [PV_LIB_SPEC_ActiveConsumption19.consume stack s a parents w es issued consumed ctx origin active]
  exact PV_LIB_SPEC_ActiveSource19.status ctx s a parents w

/-- The repaired local continuation genuinely progresses; this is not a
return-value-only adapter. It is NOT reachability from the original entry. -/
theorem nonstall (ctx : Context) (s : Store Data) (a : Nat) (parents : List Frame) (w : OWNER) :
    (PV_LIB_SPEC_ActiveConsumption19.delivered ctx s a parents w).status ≠
      .running (config s a parents PV_LIB_SPEC_Entry13.slot.source) := by
  rw [PV_LIB_SPEC_ActiveSource19.status]
  intro equal
  have waiting := congrArg (fun status => match status with
    | .running c => c.frame.waiting
    | _ => none) equal
  change none = some _ at waiting
  cases waiting

#print axioms before
#print axioms after_status
#print axioms nonstall
end PV_LIB_SPEC_ActiveCorrection19
