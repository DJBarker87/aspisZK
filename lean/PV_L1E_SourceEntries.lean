import PV_L1E_CallbackSafety
import PV_L1E_RetrySource
import PV_L1E_EntryOrder
set_option autoImplicit false
noncomputable section
namespace PV_L1E_SourceEntries
open Aeneas Aeneas.Std Result ProverRwFull
open R1Z ProverRwRetryModel ProverCommitSemanticTransport26
open PV_L1D_Logged PV_L1D_CallbackSafe
variable [ExternalTypes] [ExternalFuns]

/-- Exactly one model callback entry survives any following body outcome. -/
theorem callback_bind {X Y : Type} (k : Nat) (r : Result X)
    (f : X → Logged Y) (safe : ∀ x, Safe (f x)) :
    callbacks ((observe .callback k r >>= f).events) = [k] := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok x =>
    change callbacks ([.call .callback k] ++ (f x).events) = _
    rw [callbacks_append,safe x]
    rfl
#print axioms callback_bind

/-- Discharges the per-attempt entry premise of L1D for the composed source
interpreter. Opaque lifted native leaves still contribute no model events. -/
theorem attempt_entries {C : Type} (entropy : Entropy C) (pub : Pub)
    (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (k : Nat) (s : C × Store) :
    callbacks (PV_L1E_RetrySource.attempt entropy pub compiled variant hash k s).events = [k] := by
  unfold PV_L1E_RetrySource.attempt
  apply callback_bind
  rintro ⟨status,after⟩
  cases status with
  | Err e => exact safe_pure _
  | Ok secret =>
    apply safe_bind
    · exact PV_L1E_CallbackSafety.safe_PV_L1E_Source_070 pub compiled variant hash secret s.2
    · rintro ⟨status,store⟩
      cases status with
      | Ok proof => exact safe_pure _
      | Err e => cases e <;> exact safe_pure _
#print axioms attempt_entries

theorem successful_callbacks {C : Type} (entropy : Entropy C) (pub : Pub)
    (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (n k : Nat) (s after : C × Store) (p : ProverCommitRetry34.Published Proof)
    (success : (PV_L1D_RetryFold.run
      (PV_L1E_RetrySource.attempt entropy pub compiled variant hash) n k s).result = .ok (.done p,after)) :
    p.attempts = k + (callbacks (PV_L1D_RetryFold.run
      (PV_L1E_RetrySource.attempt entropy pub compiled variant hash) n k s).events).length :=
  PV_L1D_RetryCount.successful_callbacks _
    (attempt_entries entropy pub compiled variant hash) n k s after p success
#print axioms successful_callbacks

theorem all_outcomes {C : Type} (entropy : Entropy C) (pub : Pub)
    (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (n k : Nat) (s : C × Store) :
    ∃ m ≤ n, callbacks (PV_L1D_RetryFold.run
      (PV_L1E_RetrySource.attempt entropy pub compiled variant hash) n k s).events =
        PV_L1E_EntryOrder.entryRange k m :=
  PV_L1E_EntryOrder.all_outcomes _ (attempt_entries entropy pub compiled variant hash) n k s
#print axioms all_outcomes
end PV_L1E_SourceEntries
