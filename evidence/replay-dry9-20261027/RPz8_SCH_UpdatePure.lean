import RPz8_SCH_ChildUpdate
set_option autoImplicit false
namespace AspisR1.SCH_UpdatePure
open Aeneas Aeneas.Std Result
open SCH_ChildUpdate

theorem data (o k : AdapterRw.Ops) :
    AdapterRw.r1_pool_adapter.owned.OwnedAccount.data (update o k) =
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data o := rfl

theorem checkpoint (o k : AdapterRw.Ops) :
    AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint (update o k) =
      AdapterRw.r1_pool_adapter.owned.require_verifier_checkpoint o := rfl

theorem distinct (o k : AdapterRw.Ops) (N : Usize) :
    AdapterRw.r1_pool_adapter.owned.require_distinct_accounts (N := N) (update o k) =
      AdapterRw.r1_pool_adapter.owned.require_distinct_accounts (N := N) o := rfl

theorem pubkey (o k : AdapterRw.Ops) :
    AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (update o k) =
      AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey o := rfl

#print axioms data
#print axioms checkpoint
#print axioms distinct
#print axioms pubkey
end AspisR1.SCH_UpdatePure
