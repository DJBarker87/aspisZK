import PV_LIB_SPEC_ContextF36118
import PV_LIB_SPEC_ContextCounterPost18
import PV_LIB_SPEC_ContextCounterPost18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ContextFinalF36118
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
abbrev Input := F361.Input
abbrev Representation := F361.Representation
abbrev Pre := F361.Pre

/-- Original provider's source/representation facets remain exact. Its static
native/resources slots are replaced by the actual context machine's full
native and allocation channels, rather than identified with trigger replies. -/
def MachineSpec (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (i : Input) (m : PV_LIB_SPEC_ContextMachine18.Machine) : Prop :=
  PV_LIB_SPEC_ContextMachine18.MachineSpec cut p m ∧
  (runtime p).carrier = PV_FN_THREAD_f361.base i ∧
  (runtime p).control = i.K ∧ PV_LIB_SPEC_Full.programs = i.P ∧ @p.encode = @i.encode

def Post (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (i : Input)
    (issued : List Issued) (consumed : List Context) (candidate : Nat → Execution) : Prop :=
  PV_LIB_SPEC_ContextCounterPost18.Post cut p OwnComplete (PV_FN_THREAD_f361.entry i)
    (fun q => PV_FN_THREAD_f361.Frame i q ∧ PV_LIB_SPEC_ThreadContract.Numbered q)
    issued consumed candidate

def Contract (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (R : Representation)
    (implementation : PV_LIB_SPEC_ContextMachine18.Machine → Input → List Issued → List Context → Nat → Execution) : Prop :=
  ∀ m i issued consumed, MachineSpec cut p i m → Pre p R i →
    Post cut p i issued consumed (implementation m i issued consumed)

theorem pre_same (p : Parameters) (R : Representation) (i : Input) :
    Pre p R i ↔ F361.Pre p R i := Iff.rfl

/-- BEFORE statement retained verbatim by name; no equivalence is claimed
between the incompatible fixed-runtime and context-runtime contracts. -/
abbrev Before := F361.Contract

/-- Immediate SPEC-C17 before statement, retained unchanged. -/
abbrev CounterBefore := PV_LIB_SPEC_ContextF36118.Contract

#print axioms Input
#print axioms Representation
#print axioms Pre
#print axioms MachineSpec
#print axioms Post
#print axioms Contract
#print axioms pre_same
#print axioms Before
#print axioms CounterBefore
end PV_LIB_SPEC_ContextFinalF36118
