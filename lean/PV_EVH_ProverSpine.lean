import PV_EVH_MaskedAttempt
import PV_EVH_ReserveJoin
set_option autoImplicit false
noncomputable section
namespace PV_EVH_ProverSpine
open Aeneas Aeneas.Std ProverRwFull PV_EVH_World
open PV_EVH_Prefix (P FinishedView)
open PV_EVH_AccountEntry (Public Compiled Hash AccountInst)
open PV_EVH_RetryBody (Store Secrets Outcome)
open PV_EVH_Entropy (EntropyAnswers)
variable [ExternalTypes] [ExternalFuns]
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext

/-- Remaining head operations, with no whole prove_masked_attempt answer. -/
structure Head where
  publicBytes_OPEN : Public → P (core.result.Result (alloc.vec.Vec U8) aspis_core.state_only_prefix.r0.Error)
  hash_OPEN : Slice (Slice U8) → P (Array U8 32#usize)
  context_OPEN : Array U8 32#usize → Array U8 32#usize → P Context
  encode_OPEN : Context → P (Array U8 81#usize)
  tag_OPEN : transport.Variant → P U8

structure HeadFixed (h : Head) (hash : Hash) : Prop where
  publicBytes_fixed : ∀ p, FinishedView (h.publicBytes_OPEN p)
    (aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes p)
  hash_fixed : ∀ s, FinishedView (h.hash_OPEN s) (hash s)
  context_fixed : ∀ a b, FinishedView (h.context_OPEN a b)
    (aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1 a b)
  encode_fixed : ∀ a, FinishedView (h.encode_OPEN a)
    (aspis_core.state_only_hiding.StateOnlyHidingContext.encode a)
  tag_fixed : ∀ v, FinishedView (h.tag_OPEN v) (transport.Variant.tag v)

/-- Both whole masked entry callees are replaced by their actual source spines.
The remaining head, eighteen with-attempt and eleven reserve callees are OPEN. -/
def maskedCallees (h : Head) (b : PV_EVH_ReserveJoin.Callees)
    (r : PV_EVH_ReserveBuild.Callees) (public1 : Public) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash) : PV_EVH_MaskedAttempt.Callees where
  publicBytes_OPEN := h.publicBytes_OPEN
  hash_OPEN := h.hash_OPEN
  context_OPEN := h.context_OPEN
  encode_OPEN := h.encode_OPEN
  tag_OPEN := h.tag_OPEN
  withAttempt_OPEN := fun context binding attempt store =>
    PV_EVH_MaskedWithAttempt.run
      aspis_prover.state_only_entropy.DurableStateOnlyMaskNonceStore.Insts.Aspis_proverState_only_hidingStateOnlyMaskNonceStore
      public1 compiled variant hash context binding attempt store
      (PV_EVH_ReserveJoin.install b r)

theorem maskedCallees_fixed (h : Head) (b : PV_EVH_ReserveJoin.Callees)
    (r : PV_EVH_ReserveBuild.Callees) (public1 : Public) (compiled : Compiled)
    (variant : transport.Variant) (hash : Hash)
    (hh : HeadFixed h hash) (hb : PV_EVH_ReserveJoin.Compatible b)
    (hr : PV_EVH_ReserveBuild.Compatible r) :
    PV_EVH_MaskedAttempt.Compatible (maskedCallees h b r public1 compiled variant hash)
      public1 compiled variant hash where
  publicBytes_fixed := hh.publicBytes_fixed
  hash_fixed := hh.hash_fixed
  context_fixed := hh.context_fixed
  encode_fixed := hh.encode_fixed
  tag_fixed := hh.tag_fixed
  withAttempt_fixed := fun context binding attempt store =>
    PV_EVH_MaskedWithAttempt.run_fixed _ public1 compiled variant hash context binding attempt store
      (PV_EVH_ReserveJoin.install b r) (PV_EVH_ReserveJoin.install_fixed b r hb hr)

/-- OPEN source-spine execution, not the completed native-event producer.
Inherited entropy afterDraw, nonce helpers, retry-entry comparison op233 and
all reached allocation/drop/panic/abort coverage still require implementation. -/
def entry_OPEN {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel : Nat) (answers : EntropyAnswers)
    (public1 : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (h : Head) (b : PV_EVH_ReserveJoin.Callees) (r : PV_EVH_ReserveBuild.Callees) : P Outcome :=
  PV_EVH_AccountEntry.entry inst retryFuel entropyFuel answers public1 compiled hash store
    account account_OPEN (fun attempt store1 =>
      PV_EVH_MaskedAttempt.run public1 compiled transport.Variant.S2 hash attempt store1
        (maskedCallees h b r public1 compiled transport.Variant.S2 hash))

/-- Local erasure only. No full native observation law, actual-domain
nonemptiness, or ruling-(v') consistency discharge is implied. -/
theorem entry_fixed {T : Type} (inst : AccountInst T)
    (retryFuel entropyFuel : Nat) (answers : EntropyAnswers)
    (public1 : Public) (compiled : Compiled) (hash : Hash)
    (store : Store) (account : T) (account_OPEN : PV_EVH_AccountCallback.Account T)
    (h : Head) (b : PV_EVH_ReserveJoin.Callees) (r : PV_EVH_ReserveBuild.Callees)
    (same : ∀ n s, answers n s = getrandom.fill s)
    (account_fixed : ∀ c i, FinishedView (account_OPEN c i) (inst.call_mut c i))
    (hh : HeadFixed h hash) (hb : PV_EVH_ReserveJoin.Compatible b)
    (hr : PV_EVH_ReserveBuild.Compatible r) :
    FinishedView (entry_OPEN inst retryFuel entropyFuel answers public1 compiled hash
      store account account_OPEN h b r)
      (RealR1_client.prove_for_proof_accounts inst public1 compiled hash store account) := by
  apply PV_EVH_AccountEntry.entry_fixed
  · exact same
  · exact account_fixed
  · intro attempt store1
    exact PV_EVH_MaskedAttempt.run_fixed public1 compiled transport.Variant.S2 hash attempt store1
      (maskedCallees h b r public1 compiled transport.Variant.S2 hash)
      (maskedCallees_fixed h b r public1 compiled transport.Variant.S2 hash hh hb hr)

#print axioms maskedCallees_fixed
#print axioms entry_fixed
end PV_EVH_ProverSpine
