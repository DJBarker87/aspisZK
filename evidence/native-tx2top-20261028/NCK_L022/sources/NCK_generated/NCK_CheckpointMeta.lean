import AdapterRwCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_CheckpointMeta
open Aeneas Aeneas.Std Result
open AdapterRw.Cuts
open _root_.AdapterRw.r1_pool_adapter.owned
attribute [local irreducible] OwnedAccount.data_len
/-- Invert the actual verifier-checkpoint guard. Accepted flags/length and
same-owner comparison are outputs, not preconditions supplied to resume. -/
theorem accepted_domain (ops : _root_.AdapterRw.Ops) (a : Account)
    (program : _root_.AdapterRw.solana_pubkey.Pubkey) (writable : Bool)
    (size : ops.op12 .S2 = ok 1768#usize)
    (accepted : require_verifier_checkpoint ops a program writable = ok (.Ok ())) :
    a.is_signer = false ∧ a.executable = false ∧ a.is_writable = writable ∧
    OwnedAccount.data_len ops a = ok (.Ok 1768#usize) := by
  unfold require_verifier_checkpoint at accepted
  simp only [OwnedAccount.impl.owner, bind_tc_ok, size] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals aesop (add simp [bne_iff_ne]) (add safe [UScalar.eq_of_val_eq])
#print axioms accepted_domain
end AspisR1.NCK_CheckpointMeta
end
