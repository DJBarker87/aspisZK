import RPz8_SCH_UpdateRegistry
set_option autoImplicit false
namespace AspisR1.SCH_UpdateAuthenticate
open SCH_ChildUpdate

theorem same (o k : AdapterRw.Ops) :
    AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts (update o k) =
      AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts o := by
  unfold AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts
  simp only [SCH_UpdateRegistry.same,SCH_UpdatePure.data,SCH_UpdatePure.pubkey,
    SCH_UpdatePure.checkpoint,SCH_UpdatePure.distinct,SCH_SecondPure.readonly]
  simp only [update]

#print axioms same
end AspisR1.SCH_UpdateAuthenticate
