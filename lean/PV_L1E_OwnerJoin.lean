import PV_L1D_RetryFold
set_option autoImplicit false
namespace PV_L1E_OwnerJoin
open Aeneas Aeneas.Std Result
open R1Z.SideChannelL1AttemptRecord
open PV_L1D_Logged
variable {S P : Type}

/-- Embed the existing D163 owner without changing its record, status or state.
This is a conservative terminating submodel, not a native totality assertion. -/
def liftOwner (owner : Owner S P) : PV_L1D_RetryFold.Attempt S P :=
  fun k s => let (record,after) := owner k s
             ⟨record.events,.ok (record.result,after)⟩

/-- Full event and Result agreement for the original D163 owner, rather than
merely erasure. The same state thread and ordered records are retained. -/
theorem original_run (owner : Owner S P) (n k : Nat) (s : S) :
    PV_L1D_RetryFold.run (liftOwner owner) n k s =
      ⟨events (run owner n k s).1,
        .ok ((run owner n k s).1.result,(run owner n k s).2)⟩ := by
  induction n generalizing k s with
  | zero => rfl
  | succ n ih =>
    cases step : owner k s with
    | mk record after =>
      cases status : record.result with
      | done proof =>
        simp only [PV_L1D_RetryFold.run,liftOwner,run,step,status]
        rfl
      | stop e =>
        simp only [PV_L1D_RetryFold.run,liftOwner,run,step,status]
        rfl
      | retry =>
        simp only [PV_L1D_RetryFold.run,liftOwner,run,step,status]
        change (⟨record.events ++ (PV_L1D_RetryFold.run (liftOwner owner) n (k+1) after).events,
          (PV_L1D_RetryFold.run (liftOwner owner) n (k+1) after).result⟩ :
          Logged (R1Z.ProverCommitRetry34.Step (R1Z.ProverCommitRetry34.Published P) × S)) = _
        rw [ih]
        rfl
#print axioms original_run

/-- Every finite event prefix of the terminating submodel, without a
successful-return restriction. This does not cover outer fail/div executions. -/
theorem original_prefix (owner : Owner S P) (n k m : Nat) (s : S) :
    (PV_L1D_RetryFold.run (liftOwner owner) n k s).events.take m =
      (events (run owner n k s).1).take m := by
  rw [original_run]
#print axioms original_prefix

/-- The exact per-leaf association needed to replace the logged producer by
D163. It retains events, all ordinary error labels, and complete state. -/
def PV_L1E_Link_SourceOwner (a : PV_L1D_RetryFold.Attempt S P)
    (owner : Owner S P) : Prop := ∀ k s, a k s = liftOwner owner k s

theorem run_of_link (a : PV_L1D_RetryFold.Attempt S P) (owner : Owner S P)
    (link : PV_L1E_Link_SourceOwner a owner) (n k : Nat) (s : S) :
    PV_L1D_RetryFold.run a n k s =
      ⟨events (run owner n k s).1,
        .ok ((run owner n k s).1.result,(run owner n k s).2)⟩ := by
  have same : a = liftOwner owner := funext fun k => funext fun s => link k s
  rw [same,original_run]
#print axioms run_of_link
end PV_L1E_OwnerJoin
