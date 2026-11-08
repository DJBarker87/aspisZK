import PV_LIB_SPEC_Tls278Bound15
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_Tls278Reached15
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution initial)
open PV_LIB_SPEC_TlsNative15 (cut)

def config : Config := PV_LIB_SPEC_Tls278Lift15.config PV_LIB_SPEC_Tls59Data15.store59 5
  PV_LIB_SPEC_TlsOriginal15.parents PV_LIB_SPEC_Tls59Data15.result
def request : PV_STX2_Native.Request Data := .child PV_LIB_SPEC_Tls278Values15.token 8
  [PV_LIB_SPEC_Tls59Data15.result,PV_LIB_SPEC_Tls278Lift15.error]
def wait : PV_STX2_Native.Waiting Data := ⟨request,.child 8 (.local 5),[]⟩
def result : Data := PV_LIB_SPEC_Tls278Values15.value PV_LIB_SPEC_Entry13.slot.source

theorem waiting : config.frame.waiting = some wait := rfl

/-- The typed278 binding is applied AT the original history's step63 poll.
No reset world, fabricated parent, source-read premise or decoder premise.
The resource field may be rebound at this actual source origin. This theorem
checks the answer there; it does not yet consume it into an original64 trace. -/
theorem reached (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (resources : Resources) :
    let x := PV_LIB_SPEC_ReachedNative14.run (cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters 63
      (initial PV_LIB_SPEC_Entry14.input)
    x.state.current.status = .running config ∧
    PV_LIB_SPEC_ReachedNative14.answer (cut stack) (PV_LIB_SPEC_TlsBound15.parameters resources)
      config request x.state.current.world = some ⟨.returned (.ok result),x.state.current.world,[]⟩ := by
  dsimp only
  rw [PV_LIB_SPEC_TlsAt63.original63,PV_LIB_SPEC_TlsAt63.state63]
  refine ⟨rfl,?_⟩
  exact PV_LIB_SPEC_Tls278Bound15.answer _ resources config PV_LIB_SPEC_Entry14.state 8
    PV_LIB_SPEC_Entry13.slot.source wait waiting rfl

#print axioms config
#print axioms request
#print axioms wait
#print axioms result
#print axioms waiting
#print axioms reached
end PV_LIB_SPEC_Tls278Reached15
