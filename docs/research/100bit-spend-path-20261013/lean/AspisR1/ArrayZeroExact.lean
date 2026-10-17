import CopyEndpointExact
import ExtractedMaskConstants

/-! Shared symbolic zero initialization; reuses retained scalar constant
facts and the prior selector initializer's List.replicate proof shape. -/
set_option autoImplicit false
namespace AspisR1.ArrayZeroExact
open Aeneas Aeneas.Std
open AspisR1SelectedMaskProbe
open AspisR1.CopyEndpointExact AspisR1.ArrayUpdateCanonicalExact

theorem repeat_zero_canonical {n : Usize} :
    CanonicalArray (Array.repeat n field.QM31.ZERO) := by
  intro i
  simpa [Array.repeat_val] using AspisR1.ExtractedMaskConstants.zero_canonical

theorem repeat_zero_decoded {n : Usize} :
    decodedCells (Array.repeat n field.QM31.ZERO) = fun _ => 0 := by
  funext i
  change AspisR1.ExtractedMaskQM31Exact.decode
    ((List.replicate n.val field.QM31.ZERO)[i.val]'(by simpa using i.isLt)) = 0
  rw [List.getElem_replicate]
  exact AspisR1.ExtractedMaskConstants.zero_decode

#print axioms repeat_zero_canonical
#print axioms repeat_zero_decoded
end AspisR1.ArrayZeroExact
