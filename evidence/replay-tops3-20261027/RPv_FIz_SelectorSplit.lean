import RPv_FIv_PreparedNewTotal
import RPv_FIv_PreparedMul
import RPv_FIv_SubMap
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_SelectorSplit
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_PreparedNew (NP prepared)
open FIv_NativeValue (K Canon decode)
/-- The actual prepared product/subtraction in Native14's descending split
preserves its parent mass. Whole-loop write/canonicality still needs induction. -/
theorem value (coordinate parent right left : NQ) (p : NP)
    (hc : Canon coordinate) (hp : Canon parent)
    (hnew : field.PreparedQm31Multiplier.new coordinate=ok p)
    (hmul : field.PreparedQm31Multiplier.mul p parent=ok right)
    (hsub : field.QM31.sub parent right=ok left) :
    Canon right ∧ Canon left ∧
      decode right=decode coordinate*decode parent ∧
      decode left=decode parent-decode coordinate*decode parent ∧
      decode left+decode right=decode parent := by
  have valid := FIv_PreparedNew.valid coordinate p hc hnew
  have product := FIv_PreparedMul.value p coordinate parent right hc hp valid hmul
  have difference := FIv_SubMap.qm parent right left hp product.1 hsub
  refine ⟨product.1,difference.1,product.2,?_,?_⟩
  · rw [difference.2,product.2]
  · rw [difference.2]
    exact sub_add_cancel _ _
#print axioms value
end AspisR1.FIz_SelectorSplit
end
