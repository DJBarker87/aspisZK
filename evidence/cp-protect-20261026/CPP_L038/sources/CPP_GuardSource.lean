import Hist_Authority
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_GuardSource
open Aeneas Aeneas.Std Result AdapterRw
attribute [local instance] Classical.propDecidable

/-- Complete extracted CP guard, including error priority and arbitrary
borrow-length error. Only three independently named pure library leaves are
interpreted; no account-state, source acceptance or output law is input. -/
theorem exact (ops : AdapterRw.Ops) (account : AdapterRw.Cuts.Account)
    (id : AdapterRw.solana_pubkey.Pubkey) (writable : Bool)
    (key : ops.op36 = Hist_Authority.keyEq)
    (size : ops.op12 .S2 = ok 1768#usize)
    (clone : ∀ error, ops.op35 error = ok error) :
    AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint ops account id writable =
      if account.owner ≠ id ∨ account.is_signer = true ∨ account.executable = true ∨ account.is_writable ≠ writable then
        ok (.Err .InvalidAccountData)
      else match account.length with
        | .Err error => ok (.Err error)
        | .Ok length => if length = 1768#usize then ok (.Ok ()) else ok (.Err .InvalidAccountData) := by
  unfold AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.impl.owner
    core.cmp.impls.PartialEqShared.ne
    AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
    core.cmp.PartialEq.ne.default
  rw [key]
  unfold Hist_Authority.keyEq
  by_cases owner : account.owner = id
  all_goals cases signer : account.is_signer <;> cases executable : account.executable <;>
    cases write : account.is_writable <;> cases writable <;>
    simp only [owner,signer,executable,write,bind_tc_ok,decide_true,decide_false,Bool.not_true,Bool.not_false,
      Bool.false_eq_true,Bool.true_eq_false,Bool.false_eq_false,Bool.true_eq_true] <;>
    simp_all [AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len,size,clone]

#print axioms exact
end AspisR1.CPP_GuardSource
end
