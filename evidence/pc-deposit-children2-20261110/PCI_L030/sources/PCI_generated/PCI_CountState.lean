import PCI_Count
import PCF_CountSliceState
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCI_CountState
structure Observation (State Event : Type) where
  state : State
  events : List Event
  result : PCI_Count.ProgramResult

def run {T State Event : Type} (accounts : Slice T) (expected : Usize)
    (state : State) : Observation State Event :=
  ⟨state,[],PCI_Count.fission accounts.length expected.val⟩

/-- Full ProgramResult plus the entire unchanged state and empty effects.
    Frozen body reads only slice metadata, never an account/borrow cell. -/
theorem complete {T State Event : Type} (accounts : Slice T) (expected : Usize)
    (state : State) :
    run (Event:=Event) accounts expected state=
      ⟨state,[],PCI_Count.reply (PCF_Count.source accounts.length expected.val)⟩ := by
  unfold run
  rw [PCI_Count.all_counts]

/-- Compatibility with the adopted caller reference; the count equality is
    the representation relation on the SAME own input slice and state. -/
theorem cohort {T : Type} (accounts : Slice T) (expected : Usize) (state : PCA.PCA_State)
    (same_count : state.accountCount=accounts.length) :
    ∃ out : U8, PCF_CountSliceRef.count_reference accounts expected=ok out ∧
      PCA.countReference expected.val state=⟨state,[],PCF_CountSliceState.reply out⟩ :=
  PCF_CountSliceState.complete accounts expected state same_count

#print axioms complete
#print axioms cohort
end PCI_CountState
