import JHd_Authentication
import JHf_DomainBytes
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_AuthenticationDomain
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem preserves (ops : Ops) (verifier pool : solana_pubkey.Pubkey)
    (lane : U8) (slot : U64)
    (ma ca la ra ea : r1_pool_adapter.owned.OwnedAccount)
    (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
    (a : r1_pool_adapter.AuthenticatedAsq8Accounts)
    (accepted : JHd_Authentication.afterMaster ops verifier pool lane slot ma ca la ra ea master=
      ok (.Ok a)) :
    a.live_snapshot.deployment_domain=master.identity.deployment_domain := by
  unfold JHd_Authentication.afterMaster at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals cases accepted;rfl
#print axioms preserves
end AspisR1.JHf_AuthenticationDomain
end
