import PV_L1F_SourceRead
import PV_L1E_SourceEntries
set_option autoImplicit false
noncomputable section
namespace PV_L1F_LoggedCount
open Aeneas Aeneas.Std ProverRwFull R1Z
open ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]
/-- Bind the actual returned record to the checked logged retry on the same
source inputs. No assumption equates the source count to a native decoder. -/
theorem source_logged_count {C : Type} (entropy : Entropy C) (pub : Pub)
 (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
 (store : Store) (callback : C) (k : Usize) (n : Nat) (bound : k.val+n=8) :
 PV_L1F_ReturnedCount.sourceRead
   (prover.retry_attempt entropy pub compiled variant hash store callback k) =
 PV_L1F_ReturnedCount.read
   (PV_L1D_RetryFold.run (PV_L1E_RetrySource.attempt entropy pub compiled variant hash)
      n k.val (callback,store)).result := by
 rw [PV_L1F_SourceRead.actual_retry_count entropy pub compiled variant hash store callback k n bound]
 rw [← PV_L1E_RetrySource.run_erasure]
 rfl
#print axioms source_logged_count

/-- Actual successful return count equals the entered callback prefix length,
read from the source result before the client publishes it. -/
theorem source_count_entries {C : Type} (entropy : Entropy C) (pub : Pub)
 (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
 (store : Store) (callback : C) (k : Usize) (n : Nat) (bound : k.val+n=8)
 (p : ProverCommitRetry34.Published Proof) (after : C × Store)
 (success : (PV_L1D_RetryFold.run (PV_L1E_RetrySource.attempt entropy pub compiled variant hash)
      n k.val (callback,store)).result = .ok (.done p,after)) :
 PV_L1F_ReturnedCount.sourceRead
   (prover.retry_attempt entropy pub compiled variant hash store callback k) =
 some (k.val + (PV_L1D_CallbackSafe.callbacks
   (PV_L1D_RetryFold.run (PV_L1E_RetrySource.attempt entropy pub compiled variant hash)
      n k.val (callback,store)).events).length) := by
 rw [source_logged_count entropy pub compiled variant hash store callback k n bound,success,
   PV_L1F_ReturnedCount.read_done,
   PV_L1E_SourceEntries.successful_callbacks entropy pub compiled variant hash n k.val (callback,store) after p success]
#print axioms source_count_entries
end PV_L1F_LoggedCount
