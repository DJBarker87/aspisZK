import NNH_AuthNativeGuards
set_option autoImplicit false
namespace NNH_AuthGuardCongr
open Aeneas Aeneas.Std AdapterRw

theorem readonly (left right : Ops) (h36 : left.op36=right.op36)
 (a : r1_pool_adapter.owned.OwnedAccount) (owner : solana_pubkey.Pubkey) :
 r1_pool_adapter.owned.require_readonly_account left a owner=
 r1_pool_adapter.owned.require_readonly_account right a owner := by
 cases left
 cases right
 cases h36
 rfl

theorem checkpoint (left right : Ops) (h35 : left.op35=right.op35) (h36 : left.op36=right.op36)
 (a : r1_pool_adapter.owned.OwnedAccount) (owner : solana_pubkey.Pubkey) (writable : Bool) :
 r1_pool_adapter.owned.require_verifier_checkpoint left a owner writable=
 r1_pool_adapter.owned.require_verifier_checkpoint right a owner writable := by
 cases left
 cases right
 cases h35
 cases h36
 rfl
#print axioms readonly
#print axioms checkpoint
end NNH_AuthGuardCongr
