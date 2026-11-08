import NNQ_ObserverRegistry
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNQ_HostDigest
open Aeneas Aeneas.Std Result
variable (S : AdapterRw.Ops)
    (o : AdapterRw.SolanaDigest → Slice (Slice U8) → Result (Array U8 32#usize))

theorem authenticate_op43 :
    AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts {S with op43 := o} =
    AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts S := by
  unfold AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
  simp only [helper_0, helper_2, helper_3, helper_8, pubkey_op43, registry_op43]

theorem validate_op43 :
    AdapterRw.r1_pool_adapter.owned.validate_asq8 {S with op43 := o} =
    AdapterRw.r1_pool_adapter.owned.validate_asq8 S := by
  unfold AdapterRw.r1_pool_adapter.owned.validate_asq8
  simp only [authenticate_op43, helper_0]
#print axioms authenticate_op43
#print axioms validate_op43
end AspisR1.NNQ_HostDigest
end
