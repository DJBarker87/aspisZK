import NDO_JHe_Natives
import NDO_InstalledIdentity
set_option autoImplicit false

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

end AspisR1.NDR_CombinedAudit
