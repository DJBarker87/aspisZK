import NLQ_SnapshotFold
set_option autoImplicit false
noncomputable section
namespace NLQ_SnapshotReplay
open Aeneas Aeneas.Std Result NLM_Snapshot
/-- Reconstruct the full parent state from its OWN chronological SDK events.
Allocation aborts retain the acquired token; a failed prefix has no Drop. -/
def step (current : State) : Event → State
 | .acquire before _ _ sdk _ => {current with sdk:=sdk,next:=before.next+1}
 | .deref _ _ _ => current
 | .allocate _ _ _ _ => current
 | .release _ _ (.ok (.ok sdk)) => {current with sdk:=sdk}
 | .release _ _ _ => current
 | .returned _ _ _ _ (.ok value) => {current with owned:=current.owned++[value]}
 | .returned _ _ _ _ _ => current
def replay (initial : State) (events : List Event) : State := events.foldl step initial
/-- Composition uses the final state of the preceding prefix. -/
theorem append (initial : State) (head tail : List Event) :
 replay initial (head++tail)=replay (replay initial head) tail := by
 exact List.foldl_append
#print axioms append
end NLQ_SnapshotReplay
