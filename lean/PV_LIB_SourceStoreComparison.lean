import PV_LIB_Observation
import PV_FN_THREAD_f289_Contract
import PV_THR2_SourceStoreLibrary
set_option autoImplicit false
noncomputable section
namespace PV_LIB_SourceStoreComparison
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary

def selected (e : Entry) (reference : Data) := PV_FN_THREAD_f289.entry e [reference,.boolean true]

def original {E : Type} (C : Carrier OWNER Data) (e : Entry) (reference : Data)
    (r : Reply OWNER E Data) (events : List E) := deliver C (selected e reference) r events

def corrected {E : Type} (C : Carrier OWNER Data) (e : Entry) (w : OWNER) (reference : Data)
    (r : Reply OWNER E Data) (events : List E) : Option (PV_THR2_IntrinsicState.State OWNER E) := do
  let s ← PV_THR2_SourceStoreLibrary.PV_THR2_LibrarySemantics_CellReplace289 C
    [reference,.boolean true] e.store w
  pure (deliver C {selected e reference with store := s} r events)

/-- Comparison of the original native delivery algebra with the exact frozen
spec's CellReplace289 meaning. The reference is an entry argument, never a
supplied final Store or desired-write premise. This root-Cell component result
is not the actual f170 setter-provenance theorem. -/
theorem cell_gap {E : Type} (C : Carrier OWNER Data) (e : Entry) (w : OWNER) (reference : Data)
    (r : Reply OWNER E Data) (events : List E) (p : Address)
    (address : C.dereference w reference = some {p with fields := []})
    (before : e.store.cells {p with fields := []} = some (.boolean false))
    (outside : p.activation ≠ e.store.nextActivation)
    (destination : {p with fields := []} ≠ (⟨e.caller,e.destination,[]⟩ : Address)) :
    corrected C e w reference r events =
      some (deliver C {selected e reference with store := write e.store {p with fields := []} (some (.boolean true))} r events) ∧
    (statusStore (original C e reference r events).current.status).cells {p with fields := []} = some (.boolean false) ∧
    (statusStore (deliver C {selected e reference with store := write e.store {p with fields := []} (some (.boolean true))} r events).current.status).cells
      {p with fields := []} = some (.boolean true) := by
  refine ⟨?_,?_,?_⟩
  · unfold corrected
    rw [PV_THR2_SourceStoreLibrary.replace_root C e.store w reference (.boolean true) p address]
    rfl
  · exact ((full_reply C (selected e reference) r events).2.2.2.2
      {p with fields := []} outside destination).trans before
  · exact ((full_reply C
      {selected e reference with store := write e.store {p with fields := []} (some (.boolean true))}
      r events).2.2.2.2 {p with fields := []} outside destination).trans (write_same _ _ _)

def cell {E : Type} (p : Address) : PV_LIB.MachineObservation OWNER E → Option Data
  | .abort _ => none
  | .state q => (statusStore q.current.status).cells p

theorem running_cell {E : Type} (q : PV_THR2_IntrinsicState.State OWNER E) (c : Config)
    (running : q.current.status = .running c) (p : Address) :
    cell p (PV_LIB.observe q) = (statusStore q.current.status).cells p := by
  simp only [cell,PV_LIB.observe,PV_LIB.view,PV_LIB.statusView,PV_LIB.configView,
    PV_LIB.storeView,running,statusStore]

/-- The difference survives the public counter abstraction on a returning
reply. No post-abort state is compared or required by this theorem. -/
theorem public_gap {E : Type} (C : Carrier OWNER Data) (e : Entry) (w : OWNER) (reference : Data)
    (events : List E) (p : Address)
    (address : C.dereference w reference = some {p with fields := []})
    (before : e.store.cells {p with fields := []} = some (.boolean false))
    (outside : p.activation ≠ e.store.nextActivation)
    (destination : {p with fields := []} ≠ (⟨e.caller,e.destination,[]⟩ : Address)) :
    PV_LIB.observe (original C e reference (⟨.returned (.ok (.boolean false)),w,[]⟩ : Reply OWNER E Data) events) ≠
    PV_LIB.observe (deliver C {selected e reference with store := write e.store {p with fields := []} (some (.boolean true))}
      (⟨.returned (.ok (.boolean false)),w,[]⟩ : Reply OWNER E Data) events) := by
  let r : Reply OWNER E Data := ⟨.returned (.ok (.boolean false)),w,[]⟩
  have gap := cell_gap C e w reference r events p address before outside destination
  have oldRun : ∃ c, (original C e reference r events).current.status = .running c := by
    have shape := (full_reply C (selected e reference) r events).1
    simp only [r,expectedStatus] at shape
    exact ⟨_,shape⟩
  have newRun : ∃ c, (deliver C {selected e reference with store := write e.store {p with fields := []} (some (.boolean true))}
      r events).current.status = .running c := by
    have shape := (full_reply C {selected e reference with store := write e.store {p with fields := []} (some (.boolean true))}
      r events).1
    simp only [r,expectedStatus] at shape
    exact ⟨_,shape⟩
  obtain ⟨oldConfig,oldStatus⟩ := oldRun
  obtain ⟨newConfig,newStatus⟩ := newRun
  intro equal
  have values := congrArg (cell {p with fields := []}) equal
  rw [running_cell _ oldConfig oldStatus,running_cell _ newConfig newStatus,gap.2.1,gap.2.2] at values
  cases values
#print axioms cell_gap
#print axioms running_cell
#print axioms public_gap
end PV_LIB_SourceStoreComparison
