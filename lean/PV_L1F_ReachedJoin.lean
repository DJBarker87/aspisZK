import PV_L1E_OwnerJoin
import PV_DIAG10_Reached
set_option autoImplicit false
namespace PV_L1F_ReachedJoin
open Aeneas Aeneas.Std
open R1Z.SideChannelL1AttemptRecord
open PV_L1D_Logged
/-- Association is required only at states actually reached by normal retry
edges; it retains the whole logged leaf and full post-state. The frozen
SourceOwner and OriginalRetry links are not altered by this local criterion. -/
def ReachedOwner {S P : Type} (a : PV_L1D_RetryFold.Attempt S P)
 (owner : Owner S P) (start : Nat) (initial : S) : Prop :=
 ∀ k s, PV_DIAG10.RetryReach (fun j t => (a j t).result) start initial k s →
 a k s = PV_L1E_OwnerJoin.liftOwner owner k s

theorem reached_producer {S P : Type} (a : PV_L1D_RetryFold.Attempt S P)
 (owner : Owner S P) (start : Nat) (initial : S)
 (link : ReachedOwner a owner start initial) :
 PV_DIAG10.PV_DIAG10_Link_ReachedAttempt (fun j t => (a j t).result) start initial := by
 intro k s reached
 rw [link k s reached]
 exact ⟨_,rfl⟩
#print axioms reached_producer

theorem reached_join {S P : Type} (a : PV_L1D_RetryFold.Attempt S P)
 (owner : Owner S P) (start : Nat) (initial : S)
 (link : ReachedOwner a owner start initial) (n k : Nat) (s : S)
 (reached : PV_DIAG10.RetryReach (fun j t => (a j t).result) start initial k s) :
 PV_L1D_RetryFold.run a n k s =
 ⟨events (run owner n k s).1,.ok ((run owner n k s).1.result,(run owner n k s).2)⟩ := by
 induction n generalizing k s with
 | zero => rfl
 | succ n ih =>
   have same := link k s reached
   cases step : owner k s with
   | mk record after =>
     have leaf : a k s = ⟨record.events,.ok (record.result,after)⟩ := by
       simpa only [PV_L1E_OwnerJoin.liftOwner,step] using same
     cases status : record.result with
     | done proof => simp only [PV_L1D_RetryFold.run,leaf,status,run,step]; rfl
     | stop error => simp only [PV_L1D_RetryFold.run,leaf,status,run,step]; rfl
     | retry =>
       have edge : (a k s).result = .ok (.retry,after) := by rw [leaf,status]
       have rest := ih (k+1) after (.retry reached edge)
       simp only [PV_L1D_RetryFold.run,leaf,status,run,step]
       change (⟨record.events ++ (PV_L1D_RetryFold.run a n (k+1) after).events,
         (PV_L1D_RetryFold.run a n (k+1) after).result⟩ : Logged _) = _
       rw [rest]
       rfl
#print axioms reached_join
end PV_L1F_ReachedJoin
