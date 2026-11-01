import PV_EVH_MaskedAttempt
import PV_EVH_DurableWithAttempt
import PV_EVH_AccountFlowEntry
import PV_EVH_ProverSpine
set_option autoImplicit false
noncomputable section
namespace PV_EVH_DurableFlow
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
open PV_EVH_AccountEntry (Public Compiled Hash AccountInst)
open PV_EVH_RetryBody (Store Secrets Outcome)
open PV_EVH_Entropy (EntropyAnswers)
variable [ExternalTypes] [ExternalFuns]
open PV_EVH_ProverSpine (Head HeadFixed)

/-- Both whole masked entry callees are replaced by their actual source spines.
The remaining head, eighteen with-attempt and ten reserve callees are OPEN. -/
def maskedCallees (h : Head) (b : PV_EVH_DurableWithAttempt.Callees)
    (r : PV_EVH_DurableReserveBuild.Callees) (files : PV_EVH_NonceWorld.Answers) (public1 : Public) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) : PV_EVH_MaskedAttempt.Callees where
  publicBytes_OPEN := h.publicBytes_OPEN
  hash_OPEN := h.hash_OPEN
  context_OPEN := h.context_OPEN
  encode_OPEN := h.encode_OPEN
  tag_OPEN := h.tag_OPEN
  withAttempt_OPEN := fun context binding attempt store =>
    PV_EVH_DurableWithAttempt.run
      public1 compiled variant hash context binding attempt store
      files r b

theorem maskedCallees_fixed (h : Head) (b : PV_EVH_DurableWithAttempt.Callees)
    (r : PV_EVH_DurableReserveBuild.Callees) (files : PV_EVH_NonceWorld.Answers) (public1 : Public) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash)
    (hh : HeadFixed h hash) (hb : PV_EVH_DurableWithAttempt.Compatible b)
    (hr : PV_EVH_DurableReserveBuild.Compatible r)
    (hf : PV_EVH_NonceWorld.Compatible files) :
    PV_EVH_MaskedAttempt.Compatible (maskedCallees h b r files public1 compiled variant hash)
      public1 compiled variant hash where
  publicBytes_fixed := hh.publicBytes_fixed
  hash_fixed := hh.hash_fixed
  context_fixed := hh.context_fixed
  encode_fixed := hh.encode_fixed
  tag_fixed := hh.tag_fixed
  withAttempt_fixed := fun context binding attempt store =>
    PV_EVH_DurableWithAttempt.run_fixed public1 compiled variant hash context binding attempt store
      files r b hb hf hr

/-- OPEN source-spine execution, not the completed native-event producer.
Entropy helpers, nonce helpers, retry-entry comparison op233 and
all reached allocation/drop/panic/abort coverage still require implementation. -/
def entry_OPEN {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel : Nat) (answers : EntropyAnswers)
    (entropy : PV_EVH_EntropyStep.Callees) (nonzero_OPEN : Array U8 32#usize → P Bool)
    (public1 : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (h : Head) (b : PV_EVH_DurableWithAttempt.Callees) (r : PV_EVH_DurableReserveBuild.Callees) (files : PV_EVH_NonceWorld.Answers)
    (guard_OPEN : transport.Variant → P Bool) : P Outcome :=
  PV_EVH_AccountFlowEntry.entry inst retryFuel entropyFuel answers entropy nonzero_OPEN public1 compiled hash store
    account account_OPEN (fun attempt store1 =>
      PV_EVH_MaskedAttempt.run public1 compiled transport.Variant.S2 hash attempt store1
        (maskedCallees h b r files public1 compiled transport.Variant.S2 hash)) guard_OPEN

/-- Local erasure only. No full native observation law, actual-domain
nonemptiness, or ruling-(v') consistency discharge is implied. -/
theorem entry_fixed {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel : Nat) (answers : EntropyAnswers)
    (entropy : PV_EVH_EntropyStep.Callees) (nonzero_OPEN : Array U8 32#usize → P Bool)
    (public1 : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (h : Head) (b : PV_EVH_DurableWithAttempt.Callees) (r : PV_EVH_DurableReserveBuild.Callees) (files : PV_EVH_NonceWorld.Answers)
    (guard_OPEN : transport.Variant → P Bool)
    (he : PV_EVH_EntropyStep.Compatible entropy)
    (hn : ∀ n, FinishedView (nonzero_OPEN n) (aspis_prover.state_only_entropy.entropy_nonzero32 n))
    (guard_fixed : ∀ v, FinishedView (guard_OPEN v)
      (core.cmp.PartialEq.ne.trait_default transport.Variant.Insts.CoreCmpPartialEqVariant v transport.Variant.S2))
    (same : ∀ n s, answers n s = getrandom.fill s)
    (account_fixed : ∀ c i, FinishedView (account_OPEN c i) (inst.call_mut c i))
    (hh : HeadFixed h hash) (hb : PV_EVH_DurableWithAttempt.Compatible b)
    (hr : PV_EVH_DurableReserveBuild.Compatible r)
    (hf : PV_EVH_NonceWorld.Compatible files) :
    FinishedView (entry_OPEN inst retryFuel entropyFuel answers entropy nonzero_OPEN public1 compiled hash
      store account account_OPEN h b r files guard_OPEN)
      (RealR1_client.prove_for_proof_accounts inst public1 compiled hash store account) := by
  apply PV_EVH_AccountFlowEntry.entry_fixed
  · exact he
  · exact hn
  · exact guard_fixed
  · exact same
  · exact account_fixed
  · intro attempt store1
    exact PV_EVH_MaskedAttempt.run_fixed public1 compiled transport.Variant.S2 hash attempt store1
      (maskedCallees h b r files public1 compiled transport.Variant.S2 hash)
      (maskedCallees_fixed h b r files public1 compiled transport.Variant.S2 hash hh hb hr hf)

#print axioms maskedCallees_fixed
#print axioms entry_fixed
end PV_EVH_DurableFlow
