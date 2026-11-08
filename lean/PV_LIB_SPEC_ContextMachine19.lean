import PV_LIB_SPEC_ActiveCorrection19
import PV_LIB_SPEC_ContextCounter18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ContextMachine19
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)

/-- SPEC-C18 successor machine. Existing frontier, frame observation, boundary,
run administration and all internal histories are reused without alteration. -/
abbrev Machine := PV_LIB_SPEC_ContextMachine18.Machine
abbrev Before := PV_LIB_SPEC_ContextMachine18.MachineSpec
abbrev run := PV_LIB_SPEC_ContextMachine18.run
abbrev observe := PV_LIB_SPEC_ContextCounter18.observe
abbrev Behavior := PV_LIB_SPEC_ContextCounter18.Behavior

def MachineSpec (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) (m : Machine) : Prop :=
  m.next = PV_LIB_A_ActiveEnvironment17.step cut p

def source (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) : Machine :=
  ⟨PV_LIB_A_ActiveEnvironment17.step cut p⟩

theorem source_spec (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters) :
    MachineSpec cut p (source cut p) := rfl

theorem run_same (cut : PV_LIB_SPEC_ReachedNative14.Cut) (p : Parameters)
    (n : Nat) (x : Execution) :
    run (source cut p) n x = PV_LIB_A_ActiveEnvironment17.run cut p n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih _

/-- The row-reference machine is exactly the adopted joint-history machine
at EVERY index, including stores, events, resources and internal origins. -/
theorem history_same (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation n : Nat) :
    run (source (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame entry activation))
      PV_LIB_SPEC_ReachedEnvironment14.parameters) n
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input entry.world)) =
    PV_LIB_SPEC_ActiveAdoption19.history entry activation n := run_same _ _ _ _

/-- Before/after transport through141 only; there is no false global identity
between the repaired dispatch and the diagnosed stalling reference. -/
theorem retained_prefix (entry : PV_LIB_SPEC_EntryWorld18.Entry) (activation n : Nat)
    (bound : n ≤ 141) :
    run (source (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame entry activation))
      PV_LIB_SPEC_ReachedEnvironment14.parameters) n
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input entry.world)) =
    run (PV_LIB_SPEC_ContextMachine18.source
      (PV_LIB_SPEC_TlsNative15.cut (PV_LIB_SPEC_EntryWorld18.frame entry activation))
      PV_LIB_SPEC_ReachedEnvironment14.parameters) n
      (PV_LIB_SPEC_ResourceHistory.initial (PV_LIB_SPEC_EntryWorld18.input entry.world)) := by
  rw [history_same]
  exact (PV_LIB_SPEC_ActiveAdoption19.preserved entry activation n bound).trans
    (PV_LIB_SPEC_ContextMachine18.run_same _ _ _ _).symm

#print axioms Machine
#print axioms Before
#print axioms run
#print axioms observe
#print axioms Behavior
#print axioms MachineSpec
#print axioms source
#print axioms source_spec
#print axioms run_same
#print axioms history_same
#print axioms retained_prefix
end PV_LIB_SPEC_ContextMachine19
