import PV_L1E_SourceEntries
import PV_L1E_OwnerJoin
import PV_L1D_UploadCounts
set_option autoImplicit false
noncomputable section
namespace PV_L1E_OriginalSourceCount
open Aeneas Aeneas.Std Result ProverRwFull
open R1Z ProverRwRetryModel ProverCommitSemanticTransport26
open PV_L1D_Logged PV_L1D_CallbackSafe
open R1Z.SideChannelL1AttemptRecord (Owner run)
variable [ExternalTypes] [ExternalFuns]

/-- SAME source callback/store state, original owner, published proof and keys.
The per-leaf source/original association remains an explicit open link. This
statement combines checked source entries with the original count/account/
upload model values; it does not assert upload delivery or native traces. -/
theorem same_original_success {C Key : Type} (entropy : Entropy C) (pub : Pub)
    (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (owner : Owner (C × Store) Proof) (s after : C × Store)
    (keys : Fin 8 → Key) (p : ProverCommitRetry34.Published Proof)
    (link : PV_L1E_OwnerJoin.PV_L1E_Link_SourceOwner
      (PV_L1E_RetrySource.attempt entropy pub compiled variant hash) owner)
    (success : (PV_L1D_RetryFold.run
      (PV_L1E_RetrySource.attempt entropy pub compiled variant hash) 8 0 s).result =
        .ok (.done p,after)) :
    p.attempts = (callbacks (PV_L1D_RetryFold.run
      (PV_L1E_RetrySource.attempt entropy pub compiled variant hash) 8 0 s).events).length ∧
    ∃ k : Fin 8, k.val=p.attempts-1 ∧
      PV_L1D_SelectedCount.selected keys p.attempts (run owner 8 0 s).1.attempts.length =
        some (k.val,keys k) ∧
      ((run owner 8 0 s).1.attempts.length,
        ((run owner 8 0 s).1.attempts.filter PV_L1D_RejectionCount.retrying).length,
        PV_L1D_UploadCounts.uploads p.proof.1.length, (1 : Nat)) =
      (p.attempts,p.attempts-1,(p.proof.1.length+3762)/3763,1) := by
  constructor
  · simpa only [Nat.zero_add] using
      PV_L1E_SourceEntries.successful_callbacks entropy pub compiled variant hash 8 0 s after p success
  · rw [PV_L1E_OwnerJoin.run_of_link _ owner link] at success
    have pair : ((run owner 8 0 s).1.result,(run owner 8 0 s).2) = (.done p,after) := by
      injection success
    have original := congrArg Prod.fst pair
    obtain ⟨k,hk,selected⟩ := PV_L1D_SelectedCount.original_success owner s p keys original
    refine ⟨k,hk,selected,?_⟩
    have counts := PV_L1D_RejectionCount.original_count_pair owner s p original
    have entered := congrArg Prod.fst counts
    have rejected := congrArg Prod.snd counts
    change (run owner 8 0 s).1.attempts.length = p.attempts at entered
    change ((run owner 8 0 s).1.attempts.filter PV_L1D_RejectionCount.retrying).length = p.attempts-1 at rejected
    rw [entered,rejected,PV_L1D_UploadCounts.ceil_formula]
#print axioms same_original_success
end PV_L1E_OriginalSourceCount
