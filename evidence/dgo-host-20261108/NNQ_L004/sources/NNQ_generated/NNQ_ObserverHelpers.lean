import NNQ_Sdk
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result AdapterRw
variable (S : AdapterRw.Ops)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))

theorem helper_0 : r1_pool_adapter.owned.OwnedAccount.data {S with op43 := o} = r1_pool_adapter.owned.OwnedAccount.data S := by
  unfold r1_pool_adapter.owned.OwnedAccount.data
  repeat' first | rfl | congr 1
#print axioms helper_0

theorem helper_1 : r1_pool_adapter.owned.OwnedAccount.data_len {S with op43 := o} = r1_pool_adapter.owned.OwnedAccount.data_len S := by
  unfold r1_pool_adapter.owned.OwnedAccount.data_len
  simp only [helper_0]
  repeat' first | rfl | congr 1
#print axioms helper_1

theorem helper_2 : r1_pool_adapter.owned.require_readonly_account {S with op43 := o} = r1_pool_adapter.owned.require_readonly_account S := by
  unfold r1_pool_adapter.owned.require_readonly_account
  simp only [helper_0, helper_1]
  repeat' first | rfl | congr 1
#print axioms helper_2

theorem helper_3 : r1_pool_adapter.owned.require_verifier_checkpoint {S with op43 := o} = r1_pool_adapter.owned.require_verifier_checkpoint S := by
  unfold r1_pool_adapter.owned.require_verifier_checkpoint
  simp only [helper_0, helper_1, helper_2]
  repeat' first | rfl | congr 1
#print axioms helper_3

theorem helper_4 : r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body {S with op43 := o} = r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body S := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body
  simp only [helper_0, helper_1, helper_2, helper_3]
  repeat' first | rfl | congr 1
#print axioms helper_4

theorem helper_5 : r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0 {S with op43 := o} = r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0 S := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
  simp only [helper_0, helper_1, helper_2, helper_3, helper_4]
  repeat' first | rfl | congr 1
#print axioms helper_5

theorem helper_6 : r1_pool_adapter.owned.require_distinct_accounts_loop0.body {S with op43 := o} = r1_pool_adapter.owned.require_distinct_accounts_loop0.body S := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0.body
  simp only [helper_0, helper_1, helper_2, helper_3, helper_4, helper_5]
  repeat' first | rfl | congr 1
#print axioms helper_6

theorem helper_7 : r1_pool_adapter.owned.require_distinct_accounts_loop0 {S with op43 := o} = r1_pool_adapter.owned.require_distinct_accounts_loop0 S := by
  unfold r1_pool_adapter.owned.require_distinct_accounts_loop0
  simp only [helper_0, helper_1, helper_2, helper_3, helper_4, helper_5, helper_6]
  repeat' first | rfl | congr 1
#print axioms helper_7

theorem helper_8 : r1_pool_adapter.owned.require_distinct_accounts {S with op43 := o} = r1_pool_adapter.owned.require_distinct_accounts S := by
  unfold r1_pool_adapter.owned.require_distinct_accounts
  simp only [helper_0, helper_1, helper_2, helper_3, helper_4, helper_5, helper_6, helper_7]
  repeat' first | rfl | congr 1
#print axioms helper_8

theorem helper_9 : r1_pool_adapter.owned.authenticate_asq8_accounts {S with op43 := o} = r1_pool_adapter.owned.authenticate_asq8_accounts S := by
  unfold r1_pool_adapter.owned.authenticate_asq8_accounts
  simp only [helper_0, helper_1, helper_2, helper_3, helper_4, helper_5, helper_6, helper_7, helper_8]
  repeat' first | rfl | congr 1
#print axioms helper_9

theorem helper_10 : r1_pool_adapter.owned.validate_asq8 {S with op43 := o} = r1_pool_adapter.owned.validate_asq8 S := by
  unfold r1_pool_adapter.owned.validate_asq8
  simp only [helper_0, helper_1, helper_2, helper_3, helper_4, helper_5, helper_6, helper_7, helper_8, helper_9]
  repeat' first | rfl | congr 1
#print axioms helper_10
end AspisR1.NNQ_HostDigest
end
