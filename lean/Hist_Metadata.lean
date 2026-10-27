import Hist_Authority
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_Metadata
open Aeneas Aeneas.Std Result
open AspisR1.AdapterRw.Cuts

/-- Signer, executable and write privileges come from the real guard, for
both the writer's mutable and reader's readonly checkpoint. -/
theorem checkpoint_flags (ops : AdapterRw.Ops) (account : Account)
    (program : AdapterRw.solana_pubkey.Pubkey) (writable : Bool)
    (accepted : AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ops account program writable = ok (.Ok ())) :
    account.is_signer = false ∧ account.executable = false ∧ account.is_writable = writable := by
  unfold AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals aesop (add simp [bne_iff_ne])

/-- Pool account owner authentication uses the same concrete pure key
comparison. It does not use digest equality to identify accounts. -/
theorem readonly_owner (base : AdapterRw.Ops) (account : Account)
    (program : AdapterRw.solana_pubkey.Pubkey)
    (accepted : AdapterRw.r1_pool_adapter.owned.require_readonly_account
      (Hist_Authority.install base) account program = ok (.Ok ())) :
    account.owner = program ∧ account.is_signer = false ∧
      account.is_writable = false ∧ account.executable = false := by
  unfold AdapterRw.r1_pool_adapter.owned.require_readonly_account
    AdapterRw.r1_pool_adapter.readonly_meta_ok
    core.cmp.impls.PartialEqShared.ne
    AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
    core.cmp.PartialEq.ne.default Hist_Authority.install Hist_Authority.keyEq at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals aesop

#print axioms checkpoint_flags
#print axioms readonly_owner
end AspisR1.Hist_Metadata
end
