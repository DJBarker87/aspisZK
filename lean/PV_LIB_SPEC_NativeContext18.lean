import PV_LIB_SPEC_ValuesPrefix18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_NativeContext18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Context)

/-- All three operand/caller projections come from the CURRENT issued poll,
not a supplied request-index function or a source return marker. -/
theorem shape (x : Execution) (c : Config) (wait : PV_STX2_Native.Waiting Data) (ctx : Context)
    (origin : PV_LIB_SPEC_ResourceHistory.context x c wait = some ctx) :
    ctx.request = wait.request ∧ ctx.arguments = PV_LIB_SPEC_ResourceHistory.arguments wait.request ∧
    ctx.caller = c.frame.activation := by
  classical
  unfold PV_LIB_SPEC_ResourceHistory.context at origin
  cases found : x.issued.find? (fun issued => decide
      (issued.caller = c.frame.activation ∧ issued.request = wait.request)) with
  | none => rw [found] at origin; cases origin
  | some issued => rw [found] at origin; cases origin; exact ⟨rfl,rfl,rfl⟩

theorem bound (p : Parameters) (x : Execution) (c : Config)
    (wait : PV_STX2_Native.Waiting Data) (ctx : Context)
    (origin : PV_LIB_SPEC_ResourceHistory.context x c wait = some ctx) :
    PV_LIB_SPEC_ContextMachine18.bound p x c wait =
      some {p with resources := PV_LIB_SPEC_ResourceHistory.allocationResources p.environment ctx} := by
  unfold PV_LIB_SPEC_ContextMachine18.bound
  rw [origin]

/-- The actual Waiting request, rather than only its Context projection,
provably has no writer/Values action before85. No loop was unrolled. -/
theorem prefix_wait (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation n : Nat)
    (bound : n<85) (c : Config) (wait : PV_STX2_Native.Waiting Data) (ctx : Context)
    (ordinary : PV_LIB_SPEC_ControlRuntime.ordinary
      (PV_LIB_SPEC_History18.history entry activation n).state = some (c,wait))
    (origin : PV_LIB_SPEC_ResourceHistory.context
      (PV_LIB_SPEC_History18.history entry activation n) c wait = some ctx) :
    PV_LIB_SPEC_ValuesPrefix18.NoWriter wait.request := by
  have absent := PV_LIB_SPEC_ValuesPrefix18.poll_absent entry activation n bound c wait ctx ordinary origin
  rw [(shape _ _ _ _ origin).1] at absent
  exact absent

#print axioms shape
#print axioms bound
#print axioms prefix_wait
end PV_LIB_SPEC_NativeContext18
