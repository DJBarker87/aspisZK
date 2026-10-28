import R1Z.ProverRwBodyStore
import R1Z.ProverRwOuterGuardBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwBodyReservationTransport
open Aeneas Aeneas.Std Result ProverRwFull ProverRwBodyStore

theorem transfer {A B S : Type} (after : S) (r : Result (A × S))
    (f : A → S → Result (B × S)) (hr : Keeps after r)
    (hf : ∀ a s,Keeps s (f a s)) :
    Keeps after (r >>= fun (a,s) => f a s) := by
  cases r with
  | ok pair =>
    rcases pair with ⟨a,s⟩
    change s=after at hr
    subst s
    exact hf a after
  | fail e => trivial
  | div => trivial

variable [ExternalTypes]
section
variable [ExternalFuns]
theorem callback_writeback {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding : Array U8 32#usize) (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s context.statement_digest context.mask_nonce=.ok (accepted,after)) :
    Keeps after (ProverRwOuterAfterChecks.afterChecks store attempt hash binding context s) := by
  unfold ProverRwOuterAfterChecks.afterChecks
  rw [reservation]
  cases accepted <;> simp only [bind_tc_ok,Bool.false_eq_true,if_false,if_true]
  all_goals
    repeat' first
      | exact ok_keeps _ _
      | apply bind_keeps; intro x
      | dsimp only [Aeneas.Std.uncurry]
      | split
end

theorem body_writeback (ops : ExternalFuns) {S : Type}
    (store : aspis_prover.state_only_hiding.StateOnlyMaskNonceStore S)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (compiled : aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1)
    (v : transport.Variant) (hash : Slice (Slice U8) → Result (Array U8 32#usize))
    (binding digest : Array U8 32#usize)
    (attempt : aspis_prover.state_only_entropy.StateOnlyAttemptSecrets)
    (s after : S) (accepted : Bool)
    (reservation : store.«reserve» s digest attempt.mask_nonce=.ok (accepted,after)) :
    letI : ExternalFuns := ProverRwOuterGuardLeaves.selected ops
    Keeps after (prover.prove_masked_with_attempt store pub compiled v hash
      (ProverRwOuterContextModel.context digest attempt.mask_nonce) binding attempt s) := by
  letI : ExternalFuns := ProverRwOuterGuardLeaves.selected ops
  rw [ProverRwBodyStore.factor]
  refine transfer after _ (fun r state =>
    ProverRwBodyStoreSource.afterReserve store pub compiled v hash
      (ProverRwOuterContextModel.context digest attempt.mask_nonce) binding attempt r state) ?_ ?_
  · rw [ProverRwOuterGuardBridge.checked ops]
    exact callback_writeback store attempt hash binding _ s after accepted reservation
  · intro r state
    exact ProverRwBodyStore.continuation store pub compiled v hash _ binding attempt r state
#print axioms transfer
#print axioms callback_writeback
#print axioms body_writeback
end R1Z.ProverRwBodyReservationTransport
