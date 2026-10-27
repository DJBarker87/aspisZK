import XSc_ParseReconstruction
import XSc_ParseStage00
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSc_ParseDriver
/-- Complete 27-record actual parser to generic short-circuit fold, including
all errors/failures/divergence. Field validation is executed on both sides. -/
theorem source (bytes : Slice U8) : r1_wire.Prefix.parse bytes=XRz_ParseFold.parse bytes := by
 rw [XSc_ParseReconstruction.source]
 unfold XSc_ParseReconstruction.parse XRz_ParseFold.parse
 split
 · rfl
 · congr 1
   funext s
   congr 1
   funext root
   cases root with
   | Err e => rfl
   | Ok root =>
    rw [XSc_ParseStage00.source]
    unfold XSc_ParseResume.run
    rw [XRx_TryDriver.source]
#print axioms source
end XSc_ParseDriver
