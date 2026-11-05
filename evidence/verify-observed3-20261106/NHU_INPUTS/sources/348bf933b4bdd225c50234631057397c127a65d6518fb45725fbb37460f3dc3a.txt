import NHU_MaskHelpers
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_Linears
open AspisR1SelectedMaskProbe
abbrev QM := field.QM31
abbrev Canonical := AspisR1.ExtractedMaskTowerAdd.CanonicalQM
abbrev ReverseRange := AspisR1.ExtractedMaskReverseRange.ReverseRange
abbrev pointAt := AspisR1.ExtractedMaskLinearLoop.pointAtNat
abbrev pointValue := AspisR1.ExtractedMaskLinearLoop.pointValue
abbrev decode := AspisR1.ExtractedMaskLinearLoop.decode

def initial : ReverseRange := ⟨{start:=0#usize,«end»:=10#usize}⟩

/-- The native one-iteration certificate is threaded by the retained finite
reverse-range induction, at the SAME ten points and the actual zero seeds. -/
theorem loop (point : Array QM 10#usize)
 (canonical : ∀ i (hi : i<10),Canonical (pointAt point i hi)) :
 ∃ out,state_only_hiding.selected_mask_linears_loop initial point field.QM31.ZERO field.QM31.ZERO=ok out ∧
 Canonical out.1 ∧ Canonical out.2 ∧
 (decode out.1,decode out.2)=
 AspisR1.ExtractedMaskLinearLoop.accumulatorModel (pointValue point) 10
  (decode field.QM31.ZERO,decode field.QM31.ZERO) := by
 exact AspisR1.ExtractedMaskLinearLoop.body_loop0_model point initial 10 _ _
  rfl rfl (by decide) canonical
  AspisR1.ExtractedMaskConstants.zero_canonical
  AspisR1.ExtractedMaskConstants.zero_canonical

/-- Full emitted wrapper at the actual loop result; existing scalar packet
laws return canonical values on exactly the four logged arguments. -/
theorem result (point : Array QM 10#usize)
 (canonical : ∀ i (hi : i<10),Canonical (pointAt point i hi)) :
 ∃ out,state_only_hiding.selected_mask_linears point=ok out ∧
 Canonical out.1 ∧ Canonical out.2 ∧
 AspisR1.ExtractedMaskLinears.decode out.1=
  AspisR1.ExtractedMaskLinearRecurrence.maskLinear 0
   (AspisR1.ExtractedMaskLinearsExact.decodedPoint point) ∧
 AspisR1.ExtractedMaskLinears.decode out.2=
  AspisR1.ExtractedMaskLinearRecurrence.maskLinear 16
   (AspisR1.ExtractedMaskLinearsExact.decodedPoint point) :=
 AspisR1.ExtractedMaskLinearsExact.selected_mask_linears_exact_meaning point canonical

#print axioms loop
#print axioms result
end AspisR1.NHU_Linears
