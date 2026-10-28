import NDO_JHi_RawTerminalValidation
import NDO_JHg_Reconstruction
set_option autoImplicit false
namespace AspisR1.JHi_Reconstruction
open Aeneas Aeneas.Std Result
/-- The previously explicit raw terminal-validator observation is now derived
on the corrected expected account record and real request/scan values. -/
theorem source : JHf_ReconstructionSlot.source JHd_RequestCarrier.actual JHg_AccountValues.value
    JHd_ScanValue.candidate=ok (.Ok JGx_RealStatement.value) :=
  JHg_Reconstruction.source JHi_RawTerminalValidation.source
#print axioms source
end AspisR1.JHi_Reconstruction
