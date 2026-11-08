import PV_LIB_SPEC_ContextMachine18
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SPEC_ContextCounter18
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)

/-- SPEC-C17: use the EXISTING counter-abstracted row observation by name.
The context machine still keeps full histories internally. Origin lists and
administrative counters are not equated across D877 row implementations. -/
abbrev Observation := PV_LIB_SPEC_ThreadContract.Observation
def observe (x : Execution) : Observation := PV_LIB_SPEC_Frontier.observe x.state

def Behavior (m : PV_LIB_SPEC_ContextMachine18.Machine)
    (finish : PV_LIB_SPEC_ContextMachine18.Finish) (entry : Execution)
    (candidate : Nat → Execution) : Prop :=
  let ref := fun n => PV_LIB_SPEC_ContextMachine18.run m n entry
  (∃ n k, PV_LIB_SPEC_ContextMachine18.First m finish entry ref n ∧
    PV_LIB_SPEC_ContextMachine18.First m finish entry candidate k ∧
    observe (candidate k) = observe (ref n)) ∨
  ((∀ n, ¬ PV_LIB_SPEC_ContextMachine18.Boundary m finish entry ref n) ∧
    (∀ k, ¬ PV_LIB_SPEC_ContextMachine18.Boundary m finish entry candidate k) ∧
    (∀ n, ∃ k, (ref n).state.current.events = (candidate k).state.current.events) ∧
    (∀ k, ∃ n, (ref n).state.current.events = (candidate k).state.current.events))

/-- Two local boundary states differing only in the administrative counter.
This diagnoses the new draft, not the full joint existential. -/
def sample (counter : Nat) : Execution :=
  ⟨⟨⟨.returned (.ok .null) ⟨fun _ => none,counter⟩,PV_LIB_SPEC_Entry14.state,[]⟩,[]⟩,[],[]⟩

theorem old_distinguishes :
    PV_LIB_SPEC_ContextMachine18.observe (sample 4) ≠
    PV_LIB_SPEC_ContextMachine18.observe (sample 5) := by
  intro equal
  have counters := congrArg (fun o => match o with
    | .abort _ => 0
    | .state x => (PV_W1_LeafBoundary.statusStore x.state.current.status).nextActivation) equal
  change 4=5 at counters
  omega

theorem counter_abstracted (n m : Nat) : observe (sample n) = observe (sample m) := rfl

theorem source_cells (s : Store Data) :
    (PV_LIB_SPEC_ThreadContract.storeView s).cells = s.cells := rfl

theorem sample_histories_ignored (n : Nat) (issued consumed : Execution) :
    observe {sample n with issued := issued.issued,consumed := consumed.consumed} = observe (sample n) := rfl

theorem sample_numbered (counter : Nat) : PV_LIB_SPEC_ThreadContract.Numbered (sample counter).state := by
  constructor
  · intro c equal; cases equal
  · intro c member; cases member

theorem sample_owner (counter : Nat) (positive : 0<counter) :
    PV_FN_THREAD_OwnerWellFormed.OwnerWellFormed (sample counter).state.current.world counter :=
  PV_LIB_SPEC_EntryPre14.owner counter positive

#print axioms Observation
#print axioms observe
#print axioms Behavior
#print axioms sample
#print axioms old_distinguishes
#print axioms counter_abstracted
#print axioms source_cells
#print axioms sample_histories_ignored
#print axioms sample_numbered
#print axioms sample_owner
end PV_LIB_SPEC_ContextCounter18
