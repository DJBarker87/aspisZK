import NDO_JHi_Configuration
import NDO_JHi_Reconstruction
import NDO_JHg_InstalledValidation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHi_Validation
open Aeneas Aeneas.Std Result DrvC_Installation S2W_D189Wrappers
open _root_.AdapterRw
/-- Actual validate_asq8 control flow on the real request. Authentication is
still explicit; its complete native decoder/PDA/registry instance is open. -/
theorem source {C : Type} (c : Configuration FIo_Install.W C) (err : C) (slot : U64)
    (authentication : r1_pool_adapter.owned.authenticate_asq8_accounts
      (sdk (JHi_Configuration.value c err)) CPH_Program.verifier
      (JHg_World.e2.second secondSizes) JHb_Programs.pool 3#u8 slot=
        ok (.Ok JHg_AccountValues.value)) :
    r1_pool_adapter.owned.validate_asq8 (sdk (JHi_Configuration.value c err)) CPH_Program.verifier
      (JHg_World.e2.second secondSizes) JHb_DataRequest.value (.Ok slot)=ok (.Ok JGx_Validated.value) := by
  have reconstruction : (sdk (JHi_Configuration.value c err)).op52 JHd_RequestCarrier.actual
      JHg_AccountValues.value JHd_ScanValue.candidate=ok (.Ok JGx_RealStatement.value) := by
    rw [JHi_Configuration.reconstruction_slot]
    exact JHi_Reconstruction.source
  exact JHg_InstalledValidation.source (JHi_Configuration.base c) err slot JHg_AccountValues.value
    authentication reconstruction
#print axioms source
end AspisR1.JHi_Validation
end
