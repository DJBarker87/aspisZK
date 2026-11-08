import PV_LIB_SPEC_ContextPost18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ContextF27018
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
abbrev Input := F270.Input
abbrev Pre := F270.Pre
abbrev MachineSpec := PV_LIB_SPEC_ContextMachine18.MachineSpec
abbrev Before := F270.Contract

/-- SPEC-C14: unchanged full entry and source frame; actual context-bound v2
reference, full replies and every failure/pending/divergence arm. -/
def Post (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (i : Input)
    (issued : List Issued) (consumed : List Context) (candidate : Nat → Execution) : Prop :=
  PV_LIB_SPEC_ContextPost18.ordinary cut p PV_THR2_F270.live i issued consumed candidate

def Contract (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (implementation : PV_LIB_SPEC_ContextMachine18.Machine → Input →
      List Issued → List Context → Nat → Execution) : Prop :=
  ∀ m i issued consumed, MachineSpec cut p m → Pre p i →
    Post cut p i issued consumed (implementation m i issued consumed)

theorem pre_same (p : Parameters) (i : Input) : Pre p i ↔ F270.Pre p i := Iff.rfl

#print axioms Input
#print axioms Pre
#print axioms MachineSpec
#print axioms Before
#print axioms Post
#print axioms Contract
#print axioms pre_same
end PV_LIB_SPEC_ContextF27018
