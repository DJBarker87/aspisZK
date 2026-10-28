import NDO_JHv_SdkAuthentication
import NDO_JHi_Validation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_Validation
open Aeneas Aeneas.Std Result DrvC_Installation
open _root_.AdapterRw
open JHv_Configuration JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2

/-- Actual validate_asq8, on the same SDK, corrected world, request and slot.
Authentication, scan, reconstruction and terminal validation are all composed. -/
theorem source (base : Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : FixturePdaRuntime base) :
    r1_pool_adapter.owned.validate_asq8 (JHe_Natives.sdk (adapter base) stage)
      CPH_Program.verifier (JHg_World.e2.second S2W_D189Wrappers.secondSizes)
      JHb_DataRequest.value (.Ok slot)=ok (.Ok JGx_Validated.value) := by
  have authentication := JHv_SdkAuthentication.source base stage slot runtime
  rw [←JHv_SameSdk.sdk base stage] at authentication
  have validated := JHi_Validation.source (seed base stage) () slot authentication
  rw [JHv_SameSdk.sdk] at validated
  exact validated
#print axioms source
end AspisR1.JHv_Validation
end
