import JHv_ConfigAdapter
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHv_SameSdk
open Aeneas Aeneas.Std Result DrvC_Installation
open JHv_Configuration

/-- Reuse the generic configuration extensionality theorem. No verifier body
or concrete recurrence is unfolded to compare the other projections. -/
theorem prepared (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    prepare (seed base stage)=seed base stage := by
  apply JHe_FinalInstallation.config_ext
  · exact JHv_ConfigAdapter.source base stage
  · exact Eq.refl _
  · exact Eq.refl _
  · exact Eq.refl _
  · exact Eq.refl _
  · exact Eq.refl _
  · exact Eq.refl _
  · exact Eq.refl _
  · exact Eq.refl _
#print axioms prepared

theorem configuration (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    JHi_Configuration.value (seed base stage) ()=seed base stage := by
  change FIp_Install.configuration () (prepare (seed base stage)) (.Ok ())=seed base stage
  rw [prepared]
  exact JHe_FinalInstallation.source _ _ _
#print axioms configuration

theorem sdk (base : AdapterRw.Ops) (stage : VTop_Stages.Ops) :
    DrvC_Installation.sdk (JHi_Configuration.value (seed base stage) ())=
      JHe_Natives.sdk (adapter base) stage :=
  congrArg DrvC_Installation.sdk (configuration base stage)
#print axioms sdk
end AspisR1.JHv_SameSdk
end
