import NMB_ThreeSnapshots
set_option autoImplicit false
noncomputable section
namespace NMB_SnapshotReplay
open Aeneas Aeneas.Std Result NMB_Snapshot
/-- Prefix replay is deliberately independent of a chosen successful endpoint. -/
def step (current : State) : Event → State
 | .acquire before _ _ sdk _ => {current with sdk:=sdk,next:=before.next+1}
 | .deref _ _ _ => current
 | .allocate _ _ _ _ => current
 | .release _ _ (.ok (.ok sdk)) => {current with sdk:=sdk}
 | .release _ _ _ => current
 | .returned _ _ _ _ (.ok value) => {current with owned:=current.owned++[value]}
 | .returned _ _ _ _ _ => current
def replay (initial : State) (events : List Event) := events.foldl step initial
/-- Same-state chaining is the existing NHZ/NLD fold shape. This specialization
is needed because the per-occurrence carrier differs from NLM's Entry carrier. -/
theorem append (initial : State) (head tail : List Event) :
 replay initial (head++tail)=replay (replay initial head) tail := List.foldl_append
#print axioms append
end NMB_SnapshotReplay
