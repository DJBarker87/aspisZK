import NNQ_Sdk
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result AdapterRw
variable (S : AdapterRw.Ops)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))

theorem readonly_meta : AdapterRw.r1_pool_adapter.readonly_meta_ok {S with op43 := o} = AdapterRw.r1_pool_adapter.readonly_meta_ok S := by
  unfold AdapterRw.r1_pool_adapter.readonly_meta_ok
  rfl
#print axioms readonly_meta

theorem helper_0 : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data {S with op43 := o} = AdapterRw.r1_pool_adapter.owned.OwnedAccount.data S := by
  unfold AdapterRw.r1_pool_adapter.owned.OwnedAccount.data
  repeat' first | rfl | congr 1
#print axioms helper_0

theorem helper_1 : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len {S with op43 := o} = AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len S := by
  unfold AdapterRw.r1_pool_adapter.owned.OwnedAccount.data_len
  try simp only [helper_0]
  repeat' first | rfl | congr 1
#print axioms helper_1

theorem helper_2 : AdapterRw.r1_pool_adapter.owned.require_readonly_account {S with op43 := o} = AdapterRw.r1_pool_adapter.owned.require_readonly_account S := by
  unfold AdapterRw.r1_pool_adapter.owned.require_readonly_account
  try simp only [readonly_meta, helper_0, helper_1]
  repeat' first | rfl | congr 1
#print axioms helper_2

theorem helper_3 : AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint {S with op43 := o} = AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint S := by
  unfold AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint
  try simp only [helper_0, helper_1, helper_2]
  repeat' first | rfl | congr 1
#print axioms helper_3

theorem helper_4 {N : Usize} : AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body {S with op43 := o} (N := N) = AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body S (N := N) := by
  unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0.body
  try simp only [helper_0, helper_1, helper_2, helper_3]
  repeat' first | rfl | congr 1
#print axioms helper_4

theorem helper_5 {N : Usize} : AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0 {S with op43 := o} (N := N) = AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0 S (N := N) := by
  unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0_loop0
  try simp only [helper_0, helper_1, helper_2, helper_3, helper_4]
  repeat' first | rfl | congr 1
#print axioms helper_5

theorem helper_6 {N : Usize} : AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0.body {S with op43 := o} (N := N) = AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0.body S (N := N) := by
  unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0.body
  try simp only [helper_0, helper_1, helper_2, helper_3, helper_4, helper_5]
  repeat' first | rfl | congr 1
#print axioms helper_6

theorem helper_7 {N : Usize} : AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0 {S with op43 := o} (N := N) = AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0 S (N := N) := by
  unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts_loop0
  try simp only [helper_0, helper_1, helper_2, helper_3, helper_4, helper_5, helper_6]
  repeat' first | rfl | congr 1
#print axioms helper_7

theorem helper_8 {N : Usize} : AdapterRw.r1_pool_adapter.owned.require_distinct_accounts {S with op43 := o} (N := N) = AdapterRw.r1_pool_adapter.owned.require_distinct_accounts S (N := N) := by
  unfold AdapterRw.r1_pool_adapter.owned.require_distinct_accounts
  try simp only [helper_0, helper_1, helper_2, helper_3, helper_4, helper_5, helper_6, helper_7]
  repeat' first | rfl | congr 1
#print axioms helper_8
end AspisR1.NNQ_HostDigest
end
