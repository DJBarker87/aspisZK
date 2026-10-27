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
    change XSc_ParseCuts.tail0 bytes root 32#usize = (do
     let out ← XRx_StageFold.fold (XRz_ParseFold.step bytes) (List.range' 0 27) (.Ok ([],32#usize))
     match out with | .Err e => ok (.Err e) | .Ok state => XRz_ParseFold.finish bytes root state)
    rw [XSc_ParseStage00.source]
    unfold XSc_ParseResume.run
    rw [XRx_TryDriver.source]
    rfl
#print axioms source
end XSc_ParseDriver
