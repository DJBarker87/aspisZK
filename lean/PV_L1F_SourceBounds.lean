import PV_L1F_RetryBounds
import PV_L1F_SourceRead
set_option autoImplicit false
noncomputable section
namespace PV_L1F_SourceBounds
open Aeneas Aeneas.Std ProverRwFull R1Z ProverRwRetryModel
variable [ExternalTypes] [ExternalFuns]
/-- Actual returned-count bounds, with no original-owner or event link.
This discharges only the successful Accounts::selected numeric guard. -/
theorem actual_count_bounds {C : Type} (entropy : Entropy C) (pub : Pub)
 (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
 (store : Store) (callback : C) (k : Usize) (n : Nat) (bound : k.val+n=8)
 (count : Nat) (readout : PV_L1F_ReturnedCount.sourceRead
   (prover.retry_attempt entropy pub compiled variant hash store callback k) = some count) :
 1 ≤ count ∧ count ≤ 8 := by
 rw [PV_L1F_SourceRead.actual_retry_count entropy pub compiled variant hash store callback k n bound] at readout
 have h := PV_L1F_RetryBounds.read_bounds
   (attempt entropy pub compiled variant hash) n k.val (callback,store) count readout
 omega
#print axioms actual_count_bounds
end PV_L1F_SourceBounds
