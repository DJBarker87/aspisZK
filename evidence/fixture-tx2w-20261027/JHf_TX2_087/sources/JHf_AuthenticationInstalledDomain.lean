import JHf_KeyFixed
import JHf_AuthenticationDecodedDomain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_AuthenticationInstalledDomain
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers
open _root_.AdapterRw

def Field (ops : Ops) : Prop := ∀ master,ops.op48 JHb_DataMaster.value=ok (.Ok master) →
  master.identity.deployment_domain=JHf_DomainBytes.master

theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C)
    (lane : U8) (slot : U64) (a : r1_pool_adapter.AuthenticatedAsq8Accounts)
    (field : Field (sdk (JHf_Configuration.value c err)))
    (run : r1_pool_adapter.owned.authenticate_asq8_accounts (sdk (JHf_Configuration.value c err))
      CPH_Program.verifier (JHb_World.e2.second secondSizes) JHb_Programs.pool lane slot=ok (.Ok a)) :
    a.live_snapshot.deployment_domain=JHf_DomainBytes.master := by
  apply JHf_AuthenticationDecodedDomain.source (sdk (JHf_Configuration.value c err)) lane slot a
  · intro master decoded
    rw [JHf_KeyFixed.source] at decoded
    exact field master decoded
  · rw [JHf_KeyFixed.source]
    exact run
#print axioms source
end AspisR1.JHf_AuthenticationInstalledDomain
end
