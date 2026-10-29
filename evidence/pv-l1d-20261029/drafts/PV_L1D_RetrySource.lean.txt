import PV_L1D_RetryFold
import PV_L1D_Source_070
import PV_DIAG2_ClientRetry
set_option autoImplicit false
noncomputable section
namespace PV_L1D_RetrySource
open Aeneas Aeneas.Std Result ProverRwFull
open R1Z ProverRwRetryModel ProverCommitSemanticTransport26
open PV_L1D_Logged
variable [ExternalTypes] [ExternalFuns]
/-- The source callback and complete body on the same callback/store state.
Only the body error arm converts Rejected into retry. Leaf native prefixes
remain separate native-association obligations. -/
def attempt {C : Type} (entropy : Entropy C) (pub : Pub) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) :
    PV_L1D_RetryFold.Attempt (C × Store) Proof := fun k s => do
  let (r,after) ← observe .callback k (entropy.call_mut s.1 (ProverCommitRetrySource34.word k))
  match r with
  | .Err e => Pure.pure (.stop (error e),(after,s.2))
  | .Ok secret =>
    let (r1,store) ← PV_L1D_Source_070.produce pub compiled variant hash secret s.2
    match r1 with
    | .Ok p => Pure.pure (.done p,(after,store))
    | .Err .Rejected => Pure.pure (.retry,(after,store))
    | .Err e => Pure.pure (.stop (error e),(after,store))

theorem attempt_erasure {C : Type} (entropy : Entropy C) (pub : Pub) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) (k : Nat) (s : C × Store) :
    erase (attempt entropy pub compiled variant hash k s) =
      ProverRwRetryModel.attempt entropy pub compiled variant hash k s := by
  unfold attempt ProverRwRetryModel.attempt
  simp only [erase_bind,erase_observe]
  apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
  rintro ⟨status,after⟩ called
  cases status with
  | Err e => rfl
  | Ok secret =>
    simp only [erase_bind,PV_L1D_Source_070.complete_result]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    rintro ⟨status,store⟩ called
    cases status with
    | Ok p => rfl
    | Err e => cases e <;> rfl
#print axioms attempt_erasure

theorem run_erasure {C : Type} (entropy : Entropy C) (pub : Pub) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) (n k : Nat) (s : C × Store) :
    erase (PV_L1D_RetryFold.run (attempt entropy pub compiled variant hash) n k s) =
      ProverCommitRetry34.run (ProverRwRetryModel.attempt entropy pub compiled variant hash) n k s := by
  rw [PV_L1D_RetryFold.erasure]
  apply ProverCommitRetry34.run_congr
  intro j st
  exact attempt_erasure entropy pub compiled variant hash j st
#print axioms run_erasure

/-- Complete source Result and retained store; no publication/count erasure.
The source-to-machine step stays at V370, pending D381/D386. -/
theorem complete_source {C : Type} (entropy : Entropy C) (pub : Pub) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) (store : Store) (callback : C)
    (k : Usize) (n : Nat) (bound : k.val+n=8) :
    mapR sourceOutput (prover.retry_attempt entropy pub compiled variant hash store callback k) =
      mapR drop (erase (PV_L1D_RetryFold.run
        (attempt entropy pub compiled variant hash) n k.val (callback,store))) := by
  rw [run_erasure]
  exact ProverRwRetryModel.retry entropy pub compiled variant hash store callback k n bound
#print axioms complete_source

theorem client_no_final_rejected {C E : Type}
    (generate : C → Usize → Result (core.result.Result Secret E × C))
    (pub : Pub) (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (n k : Nat) (s : C × Store) :
    PV_DIAG2.RejectFree (erase (PV_L1D_RetryFold.run
      (attempt (PV_DIAG2.clientEntropy generate) pub compiled variant hash) n k s)) := by
  rw [run_erasure]
  exact PV_DIAG2.client_run_reject_free generate pub compiled variant hash n k s
#print axioms client_no_final_rejected
end PV_L1D_RetrySource
