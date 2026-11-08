import PV_LIB_SPEC_ContextAllocation18
import PV_LIB_SPEC_Cut92Composition
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ContextOwnInit18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution Issued Context)
abbrev Input := OwnInit.Input
abbrev Pre := OwnInit.Pre
abbrev Representation := PV_LIB_SPEC_OwnInitFull.Representation
abbrev MachineSpec := PV_LIB_SPEC_ContextMachine18.MachineSpec
abbrev Before := PV_LIB_SPEC_Cut92Composition.OwnContract

def Boundary (m : PV_LIB_SPEC_ContextMachine18.Machine) (i : Input)
    (issued : List Issued) (consumed : List Context) (trace : Nat → Execution) (n : Nat) : Prop :=
  PV_LIB_SPEC_ContextMachine18.Boundary m OwnComplete
    (PV_LIB_SPEC_ContextMachine18.start (PV_LIB_SPEC_F0Full.rootEntry i) issued consumed) trace n ∨
    ∃ k, n=k+1 ∧ PV_LIB_SPEC_OwnInitFull.InitPoll (trace k).state ∧ trace n = m.next (trace k)

def First (m : PV_LIB_SPEC_ContextMachine18.Machine) (i : Input)
    (issued : List Issued) (consumed : List Context) (trace : Nat → Execution) (n : Nat) : Prop :=
  Boundary m i issued consumed trace n ∧ ∀ k, k<n → ¬ Boundary m i issued consumed trace k

def Post (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (R : Representation) (i : Input)
    (issued : List Issued) (consumed : List Context) (candidate : Nat → Execution) : Prop :=
  let m := PV_LIB_SPEC_ContextMachine18.source cut p
  let ref := fun n => PV_LIB_SPEC_ContextMachine18.run m n
    (PV_LIB_SPEC_ContextMachine18.start (PV_LIB_SPEC_F0Full.rootEntry i) issued consumed)
  ((∃ n k, First m i issued consumed ref n ∧ First m i issued consumed candidate k ∧
      PV_LIB_SPEC_ContextMachine18.observe (candidate k) = PV_LIB_SPEC_ContextMachine18.observe (ref n) ∧
      ((∃ before, n=before+1 ∧ PV_LIB_SPEC_OwnInitFull.InitPoll (ref before).state) →
        PV_LIB_SPEC_ContextAllocation18.AllocationWitness cut p R i issued consumed ref n)) ∨
    ((∀ n, ¬ Boundary m i issued consumed ref n) ∧
      (∀ k, ¬ Boundary m i issued consumed candidate k) ∧
      (∀ n, ∃ k, (ref n).state.current.events = (candidate k).state.current.events) ∧
      (∀ k, ∃ n, (ref n).state.current.events = (candidate k).state.current.events))) ∧
  ∀ k, (∀ j, j<k → ¬ Boundary m i issued consumed candidate j) →
    ¬ PV_LIB_SPEC_Frontier.Aborts (candidate k).state →
      PV_LIB_SPEC_F0Full.RootFrame (runtime p) i (candidate k).state

def Contract (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (granted : PV_OWN2_FreshAllocation.GrantedRegions)
    (implementation : PV_LIB_SPEC_ContextMachine18.Machine → Input →
      List Issued → List Context → Nat → Execution) : Prop :=
  ∀ m i issued consumed, MachineSpec cut p m → Pre p i →
    Post cut p (OwnInit.representation p granted) i issued consumed (implementation m i issued consumed)

theorem pre_same (p : Parameters) (i : Input) : Pre p i ↔ OwnInit.Pre p i := Iff.rfl

#print axioms Input
#print axioms Pre
#print axioms Representation
#print axioms MachineSpec
#print axioms Before
#print axioms Boundary
#print axioms First
#print axioms Post
#print axioms Contract
#print axioms pre_same
end PV_LIB_SPEC_ContextOwnInit18
