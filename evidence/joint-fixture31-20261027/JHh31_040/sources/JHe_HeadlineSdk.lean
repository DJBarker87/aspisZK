import JHe_HeadlineConfiguration
import JHe_FinalInstallation
import JHe_TX1Frontier
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_HeadlineSdk
open Aeneas Aeneas.Std Result

def missing (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :=
  JHe_HeadlineConfiguration.missing (JHe_Configuration.missing (JHe_SdkLeaves.install base) stage)
def configuration (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :=
  FIp_Install.configuration () (IDa_Deployed.deployedConfiguration (missing base stage) () (.Ok ())) (.Ok ())

theorem source (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    configuration base stage=JHe_Natives.configuration base stage := by
  unfold configuration missing
  rw [←JHe_HeadlineConfiguration.installed]
  exact JHe_FinalInstallation.source _ _ _
#print axioms source

theorem sdk (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    DrvC_Installation.sdk (configuration base stage)=JHe_Natives.sdk base stage := by
  rw [source]
  rfl
#print axioms sdk

#print axioms AspisR1.JHe_TX1Frontier.wrapper_of_child
#print axioms AspisR1.JHe_FinalInstallation.source
#print axioms AspisR1.JHe_SdkCheckpoint.source
end AspisR1.JHe_HeadlineSdk
end
