import NNE_AbortIndicator
import NNE_AllocatorNecessary
import NNE_Dispatch
set_option autoImplicit false
noncomputable section
namespace NNE_AbortRollback
open Aeneas Aeneas.Std Result AspisR1 S2Trust S2W_D189Entry S2W_D189Wrappers Hist_Store

theorem reserve_false_ok (sizes : List Nat) (b : Bool)
 (h : reserve NNE_AbortIndicator.allocator sizes false = ok b) : b = false := by
 cases sizes with
 | nil => exact (Result.ok.inj h).symm
 | cons n ns => rw [NNE_AbortIndicator.reserve_false] at h; cases h

theorem no_accept (native : S2W_ExtractionBoundary.First)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (e : Entry) (p : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : Bool) :
 first native copy NNE_AbortIndicator.allocator e p data false ≠ ok (.Ok (saved,post,final)) := by
 intro accepted
 obtain ⟨b,hb,hc⟩ := NNE_AllocatorNecessary.first native copy NNE_AbortIndicator.allocator
  e p data false final saved post accepted
 have he := reserve_false_ok _ b hb
 subst b
 cases hc

theorem effect (store : Store) (call : Hir_Call.Call Bool)
 (reply : CPP_Invocation.FirstResult Bool)
 (h : ∀ saved post final, reply ≠ ok (.Ok (saved,post,final))) :
 NNE_Dispatch.view (Hir_Call.firstEffect store call reply) = (store,.rollback) := by
 cases reply with
 | fail => rfl
 | div => rfl
 | ok r =>
  cases r with
  | Err => rfl
  | Ok value => exact False.elim (h value.1 value.2.1 value.2.2 rfl)

/-- Every actually aborted invocation maps to false. Even if no snapshot
allocation was reached, false cannot commit: cleanup rejects the Ok arm. -/
theorem first (native : S2W_ExtractionBoundary.First)
 (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
 (e : Entry) (p : S2W_ExtractionBoundary.Program) (data : Slice U8)
 (store : Store) (call : Hir_Call.Call Bool) :
 NNE_Dispatch.view (Hir_Call.firstEffect store call
  (S2W_D189Wrappers.first native copy NNE_AbortIndicator.allocator e p data false)) =
 (store,.rollback) :=
 effect store call _ (no_accept native copy e p data)
#print axioms reserve_false_ok
#print axioms no_accept
#print axioms effect
#print axioms first
end NNE_AbortRollback
end
