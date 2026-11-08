import PV_LIB_SPEC_ContextF31618
import PV_LIB_SPEC_ContextCounterPost18
import PV_LIB_SPEC_ContextCounterPost18
import PV_LIB_SPEC_F316Callback
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ContextFinalF31618
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
abbrev Input := PV_LIB_SPEC_F316Callback.Input
abbrev Pre := PV_LIB_SPEC_F316Callback.Pre
abbrev MachineSpec := PV_LIB_SPEC_ContextMachine18.MachineSpec
abbrev Before := PV_LIB_SPEC_F316Callback.Contract

def Post (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (i : Input)
    (issued : List Issued) (consumed : List Context) (candidate : Nat → Execution) : Prop :=
  PV_LIB_SPEC_ContextCounterPost18.Post cut p OwnComplete (PV_LIB_SPEC_F316Callback.entry i)
    (PV_LIB_SPEC_F316Callback.Frame p i) issued consumed candidate

def Contract (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (implementation : PV_LIB_SPEC_ContextMachine18.Machine → Input →
      List Issued → List Context → Nat → Execution) : Prop :=
  ∀ m i issued consumed, MachineSpec cut p m → Pre p i →
    Post cut p i issued consumed (implementation m i issued consumed)

theorem pre_same (p : Parameters) (i : Input) :
    Pre p i ↔ PV_LIB_SPEC_F316Callback.Pre p i := Iff.rfl

/-- Immediate SPEC-C17 before statement, retained unchanged. -/
abbrev CounterBefore := PV_LIB_SPEC_ContextF31618.Contract

#print axioms Input
#print axioms Pre
#print axioms MachineSpec
#print axioms Before
#print axioms CounterBefore
#print axioms Post
#print axioms Contract
#print axioms pre_same
end PV_LIB_SPEC_ContextFinalF31618
