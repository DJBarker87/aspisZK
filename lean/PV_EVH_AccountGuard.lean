import PV_EVH_AccountCallback
import PV_EVH_PrefixRetryRun
set_option autoImplicit false
noncomputable section
namespace PV_EVH_AccountGuard
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World PV_EVH_WorldLoop
open PV_EVH_Prefix (P FinishedView)
open PV_EVH_RetryBody (Store Outcome)
open PV_EVH_PrefixRetryBody (ProveP)
open PV_EVH_Entropy (EntropyAnswers)
variable [ExternalTypes] [ExternalFuns]
abbrev Public := aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
abbrev Compiled := aspis_statement.pool_v1.pair_forest_trace.PoolV1PairForestMergedC1CompilationV1
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
abbrev AccountInst (T : Type) := core.ops.function.FnMut T Usize (Array U8 32#usize)

/-- Comparison op233/trait-default is explicitly unfinished. It can emit events
or exhaust before the actual callback; no Result-only effect credit is taken. -/
def retrying {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel : Nat) (answers : EntropyAnswers)
    (public1 : Public) (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (prove_OPEN : ProveP)
    (guard_OPEN : transport.Variant → P Bool) : P Outcome := do
  let b ← guard_OPEN variant
  if b then
    pure (.Err .Semantic,store)
  else
    PV_EVH_PrefixRetryRun.run retryFuel
      (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError inst)
      public1 compiled variant hash store account 0#usize
      (PV_EVH_AccountCallback.next inst entropyFuel answers account_OPEN) prove_OPEN

/-- This is an OPEN-callee interpretation of the extracted library entry.
It is not claimed as the complete event-producing prover worldRun. -/
def entry {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel : Nat) (answers : EntropyAnswers)
    (public1 : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (prove_OPEN : ProveP)
    (guard_OPEN : transport.Variant → P Bool) : P Outcome := do
  let (r,store1) ← retrying inst retryFuel entropyFuel answers public1 compiled
    transport.Variant.S2 hash store account account_OPEN prove_OPEN guard_OPEN
  pure (r,store1)

theorem retrying_fixed {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel : Nat) (answers : EntropyAnswers)
    (public1 : Public) (compiled : Compiled) (variant : transport.Variant) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (prove_OPEN : ProveP)
    (guard_OPEN : transport.Variant → P Bool)
    (guard_fixed : ∀ v, FinishedView (guard_OPEN v)
      (core.cmp.PartialEq.ne.trait_default transport.Variant.Insts.CoreCmpPartialEqVariant v transport.Variant.S2))
    (same : ∀ n s, answers n s = getrandom.fill s)
    (account_fixed : ∀ c i, FinishedView (account_OPEN c i) (inst.call_mut c i))
    (prove_fixed : ∀ a st, FinishedView (prove_OPEN a st)
      (prover.prove_masked_attempt public1 compiled variant hash a st)) :
    FinishedView (retrying inst retryFuel entropyFuel answers public1 compiled variant hash store account account_OPEN prove_OPEN guard_OPEN)
      (prover.prove_masked_retrying_with
        (RealR1_client.prove_for_proof_accounts.closure.Insts.CoreOpsFunctionFnMutTupleUsizeResultStateOnlyAttemptSecretsError inst)
        public1 compiled variant hash store account) := by
  unfold retrying prover.prove_masked_retrying_with
  apply PV_EVH_Prefix.bind_fixed
  · exact guard_fixed variant
  · intro b
    cases b with
    | true => exact PV_EVH_Prefix.lift_fixed _
    | false =>
      intro w r h
      exact PV_EVH_PrefixRetryRun.run_fixed retryFuel _ public1 compiled variant hash
        store account 0#usize _ prove_OPEN
        (PV_EVH_AccountCallback.next_fixed inst entropyFuel answers account_OPEN same account_fixed)
        prove_fixed w r h

theorem entry_fixed {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel : Nat) (answers : EntropyAnswers)
    (public1 : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (prove_OPEN : ProveP)
    (guard_OPEN : transport.Variant → P Bool)
    (guard_fixed : ∀ v, FinishedView (guard_OPEN v)
      (core.cmp.PartialEq.ne.trait_default transport.Variant.Insts.CoreCmpPartialEqVariant v transport.Variant.S2))
    (same : ∀ n s, answers n s = getrandom.fill s)
    (account_fixed : ∀ c i, FinishedView (account_OPEN c i) (inst.call_mut c i))
    (prove_fixed : ∀ a st, FinishedView (prove_OPEN a st)
      (prover.prove_masked_attempt public1 compiled transport.Variant.S2 hash a st)) :
    FinishedView (entry inst retryFuel entropyFuel answers public1 compiled hash store account account_OPEN prove_OPEN guard_OPEN)
      (RealR1_client.prove_for_proof_accounts inst public1 compiled hash store account) := by
  unfold entry RealR1_client.prove_for_proof_accounts
  apply PV_EVH_Prefix.bind_fixed
  · exact retrying_fixed inst retryFuel entropyFuel answers public1 compiled
      transport.Variant.S2 hash store account account_OPEN prove_OPEN guard_OPEN guard_fixed same account_fixed prove_fixed
  · rintro ⟨r,store1⟩
    exact PV_EVH_Prefix.lift_fixed _

#print axioms retrying_fixed
#print axioms entry_fixed
end PV_EVH_AccountGuard
