import PV_L1F_ReturnedCount
set_option autoImplicit false
namespace PV_L1F_RetryBounds
open Aeneas Aeneas.Std R1Z.ProverCommitRetry34
/-- Every successfully read count is bounded by control flow alone; no total
owner, source events, or native count decoder is required for this invariant. -/
theorem read_bounds {S P : Type} (attempt : Attempt S P) (n k : Nat) (s : S)
 (count : Nat) (h : PV_L1F_ReturnedCount.read (run attempt n k s)=some count) :
 k < count ∧ count ≤ k+n := by
 induction n generalizing k s with
 | zero => cases h
 | succ n ih =>
   cases leaf : attempt k s with
   | fail e => rw [run,leaf] at h; cases h
   | div => rw [run,leaf] at h; cases h
   | ok pair =>
     rcases pair with ⟨step,after⟩
     cases step with
     | done proof =>
       rw [run,leaf] at h
       change some (k+1)=some count at h
       have same := Option.some.inj h
       omega
     | stop e => rw [run,leaf] at h; cases h
     | retry =>
       rw [run,leaf] at h
       change PV_L1F_ReturnedCount.read (run attempt n (k+1) after)=some count at h
       have bounds := ih (k+1) after h
       omega
#print axioms read_bounds
end PV_L1F_RetryBounds
