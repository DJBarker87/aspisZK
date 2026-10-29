import NDO_JHv_Validation
import NDO_JHi_TX2
set_option autoImplicit false
open Lean Elab Command
run_cmd logInfo "NDR_WRAPPER_POST_IMPORT"
noncomputable section
namespace AspisR1.JHw_Wrapper
open Aeneas Aeneas.Std Result DrvC_Installation
open _root_.AdapterRw
open JHv_Configuration JHu_FixturePdaRuntime
attribute [local irreducible] JHg_World.e2

/-- Complete same-SDK wrapper composition; the three mathematical digest
certificates remain explicit until the inherited SHA realization is supplied. -/
theorem source (base : Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : FixturePdaRuntime base) (sha : JHi_SHARealization.SHARealization) :
    S2W_D189Wrappers.second (JHe_Natives.second (adapter base) stage)
      CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
      JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,())) := by
  have validation := JHv_Validation.source base stage slot runtime
  rw [←JHv_SameSdk.sdk base stage] at validation
  have wrapped := JHi_TX2.after_validation (JHi_Configuration.base (seed base stage)) () slot validation sha
  change S2W_D189Wrappers.second
    (r1_pool_adapter.owned.stage2_owned (DrvC_Installation.sdk
      (JHi_Configuration.value (seed base stage) ())))
    CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
    JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,())) at wrapped
  rw [JHv_SameSdk.sdk] at wrapped
  exact wrapped
#print axioms source
end AspisR1.JHw_Wrapper
end
