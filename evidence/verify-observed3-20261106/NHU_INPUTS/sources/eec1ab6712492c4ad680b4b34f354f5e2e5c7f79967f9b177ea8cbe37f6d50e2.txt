import NHU_MaskHelpers
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_Tower
open AspisR1.ExtractedMaskTowerAdd
abbrev QM := AspisR1SelectedMaskProbe.field.QM31
/-- Reuse the checked complete emitted four-branch law. Native conditional
word helpers are associated separately by NHU_MaskHelpers.cm_i/cm_r. The
failed monolithic word-rewriting proof is excluded, not retried. -/
theorem result (x : QM) (canonical : CanonicalQM x) (coordinate : Usize)
 (bound : coordinate.val<4) :
 ∃ out,AspisR1SelectedMaskProbe.state_only_hiding.mul_tower_basis x coordinate=ok out ∧
 CanonicalQM out ∧ wordsQM out=
  AspisR1.ExtractedMaskTowerBasis.basisWords (wordsQM x) coordinate.val :=
 AspisR1.ExtractedMaskTowerBasis.current_mul_tower_basis_words x coordinate canonical bound
#print axioms result
end AspisR1.NHU_Tower
