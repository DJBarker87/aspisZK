import XRk_DecodeModels
open Aeneas Aeneas.Std Result XRk_Release
set_option autoImplicit false
namespace LPc.View
/-- Exact modeled read set; errors and borrowed byte carriers are retained. -/
theorem readset (a b semantic y1 : Slice U8)
    (inactive : XRk_sliceRange a 7495 7527 = XRk_sliceRange b 7495 7527)
    (round0 : XRk_sliceRange a 7527 7751 = XRk_sliceRange b 7527 7751)
    (root : XRk_sliceRange a 7751 7783 = XRk_sliceRange b 7751 7783)
    (round1 : XRk_sliceRange a 7783 8007 = XRk_sliceRange b 7783 8007)
    (finalBytes : XRk_sliceRange a 8007 10055 = XRk_sliceRange b 8007 10055) :
    verifier.candidate.wide_view a semantic y1 = verifier.candidate.wide_view b semantic y1 := by
  simp only [verifier.candidate.wide_view, inactive, round0, root, round1, finalBytes]
#print axioms readset
end LPc.View
