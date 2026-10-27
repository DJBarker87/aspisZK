import Hist_Authority
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHb_GuardStd
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem key_ne_self (base : Ops) (key : solana_pubkey.Pubkey) :
    core.cmp.impls.PartialEqShared.ne
      (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey (Hist_Authority.install base)) key key = ok false := by
  simp [core.cmp.impls.PartialEqShared.ne,solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey,
    core.cmp.PartialEq.ne.default,Hist_Authority.install,Hist_Authority.keyEq]
#print axioms key_ne_self

theorem readonly (base : Ops) (a : r1_pool_adapter.owned.OwnedAccount)
    (s : a.is_signer=false) (w : a.is_writable=false) (x : a.executable=false) :
    r1_pool_adapter.owned.require_readonly_account (Hist_Authority.install base) a a.owner = ok (.Ok ()) := by
  unfold r1_pool_adapter.owned.require_readonly_account r1_pool_adapter.owned.OwnedAccount.impl.owner
  simp only [bind_tc_ok,r1_pool_adapter.readonly_meta_ok,key_ne_self,s,w,x]
  rfl
#print axioms readonly
end AspisR1.JHb_GuardStd
end
