import PV_L1F_OriginalRead
import PV_L1D_SelectedCount
import PV_L1D_RejectionCount
set_option autoImplicit false
noncomputable section
namespace PV_L1F_OriginalSelection
open Aeneas Aeneas.Std ProverRwFull R1Z
open ProverRwRetryModel SideChannelL1AttemptRecord
variable [ExternalTypes] [ExternalFuns]
/-- Bounds and account index from an actually read source count, retaining
only original control association. This is value-level account selection,
not JSON delivery, world order or witness-independent occurrence. -/
theorem actual_count_selects {C Key : Type} (entropy : Entropy C) (pub : Pub)
 (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
 (owner : Owner (C × Store) Proof)
 (control : PV_L1E_SourceOwnerLinks.PV_L1E_Link_OwnerControl entropy pub compiled variant hash owner)
 (store : Store) (callback : C) (k : Usize) (zero : k.val=0)
 (keys : Fin 8 → Key) (count : Nat)
 (readout : PV_L1F_ReturnedCount.sourceRead
   (prover.retry_attempt entropy pub compiled variant hash store callback k) = some count) :
 1 ≤ count ∧ count ≤ 8 ∧
 ∃ j : Fin 8, j.val=count-1 ∧
   PV_L1D_SelectedCount.selected keys count
     (run owner 8 0 (callback,store)).1.attempts.length=some (j.val,keys j) ∧
   ((run owner 8 0 (callback,store)).1.attempts.length,
    ((run owner 8 0 (callback,store)).1.attempts.filter PV_L1D_RejectionCount.retrying).length) =
      (count,count-1) := by
 obtain ⟨p,hp,hcount⟩ := PV_L1F_OriginalRead.original_success_of_read entropy pub compiled variant hash owner control store callback k 8 (by omega) count readout
 rw [zero] at hp
 obtain ⟨lo,hi⟩ := PV_L1D_CountSuccess.count_bounds owner (callback,store) p hp
 obtain ⟨j,hj,selected⟩ := PV_L1D_SelectedCount.original_success owner (callback,store) p keys hp
 have counts := PV_L1D_RejectionCount.original_count_pair owner (callback,store) p hp
 rw [hcount] at lo hi hj selected counts
 exact ⟨lo,hi,j,hj,selected,counts⟩
#print axioms actual_count_selects
end PV_L1F_OriginalSelection
