import PV_L1G_WorldJoin
import PV_L1F_ReachedJoin
set_option autoImplicit false
namespace PV_L1G_WorldRetry
variable {W S P : Type}
/-- Original D163 association on the reached world/state pairs is sufficient
for ordered calls and complete Result. This does not assert that those native
leaf associations hold, or erase the separate failure-world boundary. -/
theorem original_logged (a : Attempt W S P)
 (owner : R1Z.SideChannelL1AttemptRecord.Owner (W × S) P)
 (start : Nat) (initial : W × S)
 (link : PV_L1F_ReachedJoin.ReachedOwner (stateAttempt a) owner start initial)
 (n k : Nat) (s : S) (w : W)
 (reached : PV_DIAG10.RetryReach (fun j ws => (stateAttempt a j ws).result)
   start initial k (w,s)) :
 stateLog (run a n k s w) =
 ⟨R1Z.SideChannelL1AttemptRecord.events
   (R1Z.SideChannelL1AttemptRecord.run owner n k (w,s)).1,
   .ok ((R1Z.SideChannelL1AttemptRecord.run owner n k (w,s)).1.result,
     (R1Z.SideChannelL1AttemptRecord.run owner n k (w,s)).2)⟩ := by
 rw [logged_join]
 exact PV_L1F_ReachedJoin.reached_join (stateAttempt a) owner start initial link n k (w,s) reached
#print axioms original_logged
end PV_L1G_WorldRetry
