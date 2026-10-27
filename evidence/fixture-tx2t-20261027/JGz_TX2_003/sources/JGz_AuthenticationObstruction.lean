import JGz_AccountOwners
import Hist_Asq8Guards
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGz_AuthenticationObstruction
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_D189Wrappers

theorem source (base : AdapterRw.Ops) (proofAccount : Slice U8)
    (pool : AdapterRw.solana_pubkey.Pubkey) (lane : U8) (slot : U64)
    (out : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts)
    (different : pool≠CPH_Program.verifier) :
    AdapterRw.r1_pool_adapter.owned.authenticate_asq8_accounts (Hist_Authority.install base)
      CPH_Program.verifier ((JFv_World.e2 proofAccount).second secondSizes) pool lane slot ≠ ok (.Ok out) := by
  intro accepted
  obtain ⟨master,forest,selected,checkpoint,im,_,_,_,_,guard,_,_⟩ :=
    Hist_Asq8Guards.guards (Hist_Authority.install base) _ pool _ lane slot out accepted
  have same : master=(JFv_World.e2 proofAccount).snapshot 1 384 384 :=
    Result.ok.inj (im.symm.trans (JGz_AccountOwners.master_index proofAccount))
  subst master
  exact JGz_AccountOwners.master_rejects base proofAccount pool different guard
#print axioms source
end AspisR1.JGz_AuthenticationObstruction
end
