import NLQ_SnapshotReplay
import NLM_SnapshotPrefix
set_option autoImplicit false
noncomputable section
namespace NLQ_ReplayAbort
open Aeneas Aeneas.Std Result NLM_Snapshot
/-- The allocation prefix ends with its shared token LIVE. In particular,
replaying a fail/div prefix does not silently release a guard. -/
theorem allocation (s : State) (a : Nat) (reply : Result Unit) :
 NLQ_SnapshotReplay.replay s (allocationPrefix s a reply)=
 {s with sdk:=NLM_Snapshot.acquired s a,next:=s.next+1} := by
 rfl
#print axioms allocation
end NLQ_ReplayAbort
