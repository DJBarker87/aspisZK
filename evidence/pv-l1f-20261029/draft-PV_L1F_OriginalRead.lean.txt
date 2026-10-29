import PV_L1F_SourceRead
import PV_L1E_SourceOwnerLinks
set_option autoImplicit false
noncomputable section
namespace PV_L1F_OriginalRead
open Aeneas Aeneas.Std ProverRwFull R1Z
open ProverRwRetryModel SideChannelL1AttemptRecord
variable [ExternalTypes] [ExternalFuns]
/-- Only the unchanged complete control/state link is used for this value
projection. Native event association is still required for the trace links. -/
theorem original_read {C : Type} (entropy : Entropy C) (pub : Pub)
 (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
 (owner : Owner (C × Store) Proof)
 (control : PV_L1E_SourceOwnerLinks.PV_L1E_Link_OwnerControl entropy pub compiled variant hash owner)
 (store : Store) (callback : C) (k : Usize) (n : Nat) (bound : k.val+n=8) :
 PV_L1F_ReturnedCount.sourceRead
   (prover.retry_attempt entropy pub compiled variant hash store callback k) =
 returnedAttempts (run owner n k.val (callback,store)).1 := by
 rw [PV_L1F_SourceRead.actual_retry_count entropy pub compiled variant hash store callback k n bound]
 have same := ProverCommitRetry34.run_congr
   (ProverRwRetryModel.attempt entropy pub compiled variant hash) (eraseOwner owner) control n k.val (callback,store)
 rw [same,SideChannelL1AttemptRecord.erase_run]
 unfold returnedAttempts
 cases (run owner n k.val (callback,store)).1.result <;> rfl
#print axioms original_read

/-- Original success is learned from the actual field-read outcome rather
than assumed from an event decoder. Failure/divergence do not yield a count. -/
theorem original_success_of_read {C : Type} (entropy : Entropy C) (pub : Pub)
 (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
 (owner : Owner (C × Store) Proof)
 (control : PV_L1E_SourceOwnerLinks.PV_L1E_Link_OwnerControl entropy pub compiled variant hash owner)
 (store : Store) (callback : C) (k : Usize) (n : Nat) (bound : k.val+n=8)
 (count : Nat) (readout : PV_L1F_ReturnedCount.sourceRead
   (prover.retry_attempt entropy pub compiled variant hash store callback k) = some count) :
 ∃ p : ProverCommitRetry34.Published Proof,
   (run owner n k.val (callback,store)).1.result = .done p ∧ p.attempts=count := by
 rw [original_read entropy pub compiled variant hash owner control store callback k n bound] at readout
 cases h : (run owner n k.val (callback,store)).1.result with
 | done p =>
   refine ⟨p,by simp only [h],?_⟩
   simpa only [returnedAttempts,h,Option.some.injEq] using readout
 | stop e => simp only [returnedAttempts,h] at readout; cases readout
 | retry => simp only [returnedAttempts,h] at readout; cases readout
#print axioms original_success_of_read
end PV_L1F_OriginalRead
