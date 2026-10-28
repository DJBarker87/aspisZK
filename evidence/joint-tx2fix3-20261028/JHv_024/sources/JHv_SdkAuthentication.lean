import JHv_SameSdk
import JHv_Authentication
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_SdkAuthentication
open Aeneas Aeneas.Std Result DrvC_Installation
open _root_.AdapterRw
open JHv_Configuration JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2

/-- Actual SDK authentication, with the same retained slot and data inputs.
The outer reference installation is erased using the existing field laws. -/
theorem source (base : Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : FixturePdaRuntime base) :
    r1_pool_adapter.owned.authenticate_asq8_accounts
      (JHe_Natives.sdk (adapter base) stage) CPH_Program.verifier
      (JHg_World.e2.second S2W_D189Wrappers.secondSizes) JHb_Programs.pool 3#u8 slot=
        ok (.Ok JHg_AccountValues.value) := by
  let ops := JHe_Natives.sdk (adapter base) stage
  have retained : FixturePdaRuntime ops := runtime
  have registry := JHv_RegistryCaller.source ops slot retained
    JHv_LeafObservations.policy (congrArg ok JHv_Leaves.loader_fixture)
    (NCX_JHuObservations.registry _) JHv_LeafObservations.immutable
    JHv_LeafObservations.unrevoked (NCX_JHuObservations.entry _) (JHv_LeafObservations.active slot)
  have auth := JHj_Authentication.source ops slot JHu_Master.observation
    (JHu_PdaObservations.master ops retained) registry JHu_Checkpoint.observation
    (JHu_PdaObservations.checkpoint ops retained) JHu_Lane.observation
    (JHu_PdaObservations.lane ops retained)
  have fixed := JHf_ReferenceFixed.source (JHi_Configuration.base (seed base stage)) ()
  change JHd_ReferenceSlots.install (DrvC_Installation.sdk (JHi_Configuration.value (seed base stage) ()))=
    DrvC_Installation.sdk (JHi_Configuration.value (seed base stage) ()) at fixed
  rw [JHv_SameSdk.sdk] at fixed
  rw [fixed] at auth
  exact auth
#print axioms source
end AspisR1.JHv_SdkAuthentication
end
