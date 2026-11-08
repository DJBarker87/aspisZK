import PV_LIB_SPEC_ScopeAllocationPollGap
import PV_LIB_SPEC_V2Runtime
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ScopeRuntimeGap
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ScopeAllocationGap PV_LIB_SPEC_ScopeAllocationPollGap
/-- Keep the concrete source carrier/control but quantify EVERY native/backend
schedule. Source failure below cannot be blamed on the old pending example. -/
def parameters (resources : Resources) (environment : Environment) : Parameters :=
  {PV_LIB_SPEC_ConcreteEntry.parameters with resources := resources,environment := environment}

theorem native_none (resources : Resources) (environment : Environment)
    (c : Config) (w : OWNER) (thread panicked : Data) (a p : Nat)
    (allocated : (resources (.malloc 48) (world w)).answer = .returned (.ok p))
    (nonnull : p ≠ 0) :
    PV_LIB_SPEC_SparseRuntime.native (parameters resources environment) c
      (request {c.store with nextActivation := a} thread panicked) w = none := by
  unfold PV_LIB_SPEC_SparseRuntime.native
  change PV_LIB_SPEC_SparsePacketHandler.handler C K resources
    PV_LIB_SPEC_ConcreteEntry.parameters.encode {c.store with nextActivation := a} _
    (request {c.store with nextActivation := a} thread panicked) w = none
  exact rejects resources _ _ _ w thread panicked p allocated nonnull

theorem answer_none (resources : Resources) (environment : Environment)
    (c : Config) (w : OWNER) (thread panicked : Data) (a p : Nat)
    (allocated : (resources (.malloc 48) (world w)).answer = .returned (.ok p))
    (nonnull : p ≠ 0) :
    PV_LIB_SPEC_SparseRuntime.answer (parameters resources environment) c
      (request {c.store with nextActivation := a} thread panicked) w = none := by
  unfold PV_LIB_SPEC_SparseRuntime.answer PV_LIB_SPEC_SparseRuntime.valueAnswer
  rw [native_none resources environment c w thread panicked a p allocated nonnull]
  rfl

#print axioms parameters
#print axioms native_none
#print axioms answer_none
end PV_LIB_SPEC_ScopeRuntimeGap
