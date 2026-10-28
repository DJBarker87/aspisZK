import Lean
import RPx_Deployed
import NDO_Joint
import NDO_InstalledIdentity
set_option autoImplicit false
open Lean Elab Command

namespace AspisR1.NDR_CombinedAudit
open Aeneas Aeneas.Std Result
/-- The exact installed configuration underlying the witness's first and second
native functions is the headline's final FIp/IDa configuration at these data. -/
theorem fixtureInstalled (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    JHe_Natives.configuration base stage =
      FIp_Install.configuration ()
        (IDa_Deployed.deployedConfiguration
          (NDO_InstalledIdentity.missing
            (JHe_Configuration.missing (JHe_SdkLeaves.install base) stage))
          () (.Ok ())) (.Ok ()) := by
  exact (NDO_InstalledIdentity.finalInstalled
    (JHe_Configuration.missing (JHe_SdkLeaves.install base) stage) () (.Ok ())).symm
#print axioms fixtureInstalled

noncomputable def headlineSdk (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :=
  DrvC_Installation.sdk
    (FIp_Install.configuration ()
      (IDa_Deployed.deployedConfiguration
        (NDO_InstalledIdentity.missing
          (JHe_Configuration.missing (JHe_SdkLeaves.install base) stage))
        () (.Ok ())) (.Ok ()))

theorem firstNative (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    JHe_Natives.first base stage =
      AdapterRw.r1_pool_adapter.owned.stage1_owned (headlineSdk base stage) := by
  unfold JHe_Natives.first JHe_Natives.sdk headlineSdk
  rw [fixtureInstalled]
#print axioms firstNative

theorem secondNative (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    JHe_Natives.second base stage =
      AdapterRw.r1_pool_adapter.owned.stage2_owned (headlineSdk base stage) := by
  unfold JHe_Natives.second JHe_Natives.sdk headlineSdk
  rw [fixtureInstalled]
#print axioms secondNative

/-- The original joint witness, with both native arguments explicitly presented
through the headline's installed configuration. All fixture/runtime premises and
saved-byte conclusions are retained. -/
theorem sourceOnHeadline
    (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) (slot : U64)
    (runtime : JHu_FixturePdaRuntime.FixturePdaRuntime base) :
    ∃ saved : alloc.vec.Vec U8,
      S2W_D189Wrappers.first
        (AdapterRw.r1_pool_adapter.owned.stage1_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.copy CPH_FixtureData.allocator JHb_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHe_WrapperReady.post saved,())) ∧
      S2W_D189Wrappers.first
        (AdapterRw.r1_pool_adapter.owned.stage1_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.copy CPH_FixtureData.allocator JHg_World.e1
        CPH_Program.verifier JHe_Natives.data1 ()=
          ok (.Ok (saved,JHk_WorldFirst.post saved,())) ∧
      saved.val=JFx_NativeBytes.checkpoint.val ∧ saved.val.length=1768 ∧
      S2W_D189Wrappers.second
        (AdapterRw.r1_pool_adapter.owned.stage2_owned
          (headlineSdk (JHv_Configuration.adapter base) stage))
        CPH_FixtureData.allocator JHg_World.e2 CPH_Program.verifier
        JHb_DataRequest.value (.Ok slot) ()=ok (.Ok (JHg_World.e2.heap,())) := by
  simpa only [firstNative, secondNative] using NDO_Joint.source base stage slot runtime
#print axioms sourceOnHeadline
end AspisR1.NDR_CombinedAudit

-- Submit only after every NDO witness dependency passes.
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NDO_Joint.source
#print axioms AspisR1.NDO_InstalledIdentity.finalInstalled
run_cmd do
  let env := (← getEnv).setExporting false
  for root in #[`AspisR1.RPx_Deployed.deployed, `AspisR1.NDO_Joint.source] do
    let some info := env.checked.get.find? root | throwError "missing root {root}"
    let constants := info.type.getUsedConstants
    for required in #[`AspisR1.S2W_D189Wrappers.first, `AspisR1.S2W_D189Wrappers.second] do
      unless constants.contains required do
        throwError "root {root} does not directly mention {required}"
    logInfo m!"NDR_SAME_WRAPPER_CONSTANTS {root}"
  logInfo m!"NDR_CLOSURE_MODULE_COUNT {env.header.modules.size}"
  logInfo "NDR_COMBINED_COMPLETE"
