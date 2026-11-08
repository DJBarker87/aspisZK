import PV_LIB_Graph
import PV_W1_LeafBoundary
set_option autoImplicit false
namespace PV_LIB
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine

/-- Canonical representative modulo the administrative activation counter.
Numbering is a separate machine invariant, never inferred from this zero. -/
def storeView (s : Store Data) : Store Data := {s with nextActivation := 0}
def configView (c : Config) : Config := {c with store := storeView c.store}
def statusView : Status → Status
  | .running c => .running (configView c)
  | .returned r s => .returned r (storeView s)
  | .fault f s => .fault f (storeView s)
  | .undefined a s => .undefined a (storeView s)
def view {W E : Type} (q : PV_THR2_IntrinsicState.State W E) :=
  ({current := {q.current with status := statusView q.current.status},
    suspended := q.suspended.map configView} : PV_THR2_IntrinsicState.State W E)

theorem store_cells (s : Store Data) : (storeView s).cells = s.cells := rfl
theorem counter_irrelevant (s : Store Data) (n : Nat) :
    storeView {s with nextActivation := n} = storeView s := rfl
theorem world_events {W E : Type} (q : PV_THR2_IntrinsicState.State W E) :
    (view q).current.world = q.current.world ∧
      (view q).current.events = q.current.events := ⟨rfl,rfl⟩

#print axioms store_cells
#print axioms counter_irrelevant
#print axioms world_events
end PV_LIB
