import NMT_345CanonicalContainers
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result AspisR1
abbrev CanonicalStatement := AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1

def PaymentDomains : CanonicalStatement → Prop
 | .PrivateTransfer _ p => NJX_DigestCohort.dc p.anchor_root ∧ NJX_DigestCohort.dc p.nullifier ∧
    NJX_DigestCohort.dc p.recipient_commitment ∧ NJX_DigestCohort.dc p.change_commitment
 | .Withdrawal _ p => NJX_DigestCohort.dc p.anchor_root ∧ NJX_DigestCohort.dc p.nullifier ∧
    NJX_DigestCohort.dc p.change_commitment
/-- This is an internal returning-step invariant, not a row-root premise.
No216-byte payment encoding is normalized to derive these guards. -/
theorem payment_domains (s : CanonicalStatement)
 (good : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 s = .ok (.Ok ())) :
 PaymentDomains s := by
 obtain ⟨bytes,pay,_⟩ := NFY_NBN_StatementDomains.payment_reached s good
 cases s with
 | PrivateTransfer c p =>
  change AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_private_transfer_public_v1 p = .ok (.Ok bytes) at pay
  rw [NFY_NBP_TransferEncode.result] at pay
  unfold NFY_NBP_PaymentModel.transfer_encoded at pay
  cases h : NFY_NBG_PaymentValidators.transfer p with
  | Err e => simp only [h] at pay; cases pay
  | Ok u =>
   cases u
   have hc := transfer_canonical p h
   exact ⟨canonical_bool_members _ hc.1,canonical_bool_members _ hc.2.1,
     canonical_bool_members _ hc.2.2.1,canonical_bool_members _ hc.2.2.2⟩
 | Withdrawal c p =>
  change AspisR1TerminalDecoder.pool_v1.payment_relation.encode_pool_v1_withdrawal_public_v1 p = .ok (.Ok bytes) at pay
  rw [NFY_NBP_WithdrawalEncode.result] at pay
  unfold NFY_NBP_PaymentModel.withdrawal_encoded at pay
  cases h : NFY_NBG_PaymentValidators.withdrawal p with
  | Err e => simp only [h] at pay; cases pay
  | Ok u =>
   cases u
   have hc := withdrawal_canonical p h
   exact ⟨canonical_bool_members _ hc.1,canonical_bool_members _ hc.2.1,
     canonical_bool_members _ hc.2.2⟩
#print axioms payment_domains
end NMT_345
