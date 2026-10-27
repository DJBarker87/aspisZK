import JHf_AuthenticationDomain
import JHd_AuthenticationPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_AuthenticationDecodedDomain
open Aeneas Aeneas.Std Result S2W_D189Wrappers
open _root_.AdapterRw

theorem afterRead (ops : Ops) (verifier pool : solana_pubkey.Pubkey)
    (lane : U8) (slot : U64) (ma ca la ra ea : r1_pool_adapter.owned.OwnedAccount)
    (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
    (a : r1_pool_adapter.AuthenticatedAsq8Accounts)
    (decoded : ops.op48 JHb_DataMaster.value=ok (.Ok master))
    (domain : master.identity.deployment_domain=JHf_DomainBytes.master)
    (run : JHd_Authentication.afterRead ops verifier pool lane slot ma ca la ra ea=ok (.Ok a)) :
    a.live_snapshot.deployment_domain=JHf_DomainBytes.master := by
  unfold JHd_Authentication.afterRead at run
  rw [decoded,bind_tc_ok] at run
  exact (JHf_AuthenticationDomain.preserves ops verifier pool lane slot ma ca la ra ea master a run).trans domain
#print axioms afterRead

theorem source (base : Ops) (lane : U8) (slot : U64)
    (a : r1_pool_adapter.AuthenticatedAsq8Accounts)
    (field : ∀ master,(JHd_KeyStd.install base).op48 JHb_DataMaster.value=ok (.Ok master) →
      master.identity.deployment_domain=JHf_DomainBytes.master)
    (run : r1_pool_adapter.owned.authenticate_asq8_accounts (JHd_KeyStd.install base)
      CPH_Program.verifier (JHb_World.e2.second secondSizes) JHb_Programs.pool lane slot=ok (.Ok a)) :
    a.live_snapshot.deployment_domain=JHf_DomainBytes.master := by
  rw [JHd_AuthenticationPrefix.source] at run
  unfold JHd_Authentication.afterRead at run
  cases decoded : (JHd_KeyStd.install base).op48 JHb_DataMaster.value with
  | fail e=>simp only [decoded,bind_tc_fail] at run;cases run
  | div=>simp only [decoded,bind_tc_div] at run;cases run
  | ok result=>
    cases result with
    | Err e=>simp only [decoded,bind_tc_ok] at run;cases run
    | Ok master=>
      simp only [decoded,bind_tc_ok] at run
      exact (JHf_AuthenticationDomain.preserves _ _ _ _ _ _ _ _ _ _ master a run).trans
        (field master decoded)
#print axioms source
end AspisR1.JHf_AuthenticationDecodedDomain
end
