-- UNCHECKED diagnostic draft: host admission/collection failed before compilation.
-- Not an accepted theorem or axiom-audit result; see CDX_FINDING.md Q2.
import RPz7_AspisR1CircleSampleWrapper_RawCircleSampleActualFallbackResultV4

set_option autoImplicit false
noncomputable section
namespace CDX.Fallback
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerCirclePolicy
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerClosureProductExecution (encode)
open R0P.SemSource

def x0 : QM31Exact := ⟨⟨429496729,1288490188⟩,⟨0,0⟩⟩
def y0 : QM31Exact := ⟨⟨0,0⟩,⟨429496730,1288490188⟩⟩
def x1 : QM31Exact := ⟨⟨1420643028,1949254387⟩,⟨1123299138,892031669⟩⟩
def y1 : QM31Exact := ⟨⟨627725989,561649569⟩,⟨396458520,693802409⟩⟩

-- Four-limb products only: certify the native numerators without evaluating inverses.
theorem numerator_x0 : x0 * (1 + circleFallbackParameter0^2) =
    1 - circleFallbackParameter0^2 := by decide
theorem numerator_y0 : y0 * (1 + circleFallbackParameter0^2) =
    2 * circleFallbackParameter0 := by decide
theorem numerator_x1 : x1 * (1 + circleFallbackParameter1^2) =
    1 - circleFallbackParameter1^2 := by decide
theorem numerator_y1 : y1 * (1 + circleFallbackParameter1^2) =
    2 * circleFallbackParameter1 := by decide

private theorem point_of_products (t x y : QM31Exact) (hd : 1+t^2 ≠ 0)
    (hx : x*(1+t^2) = 1-t^2) (hy : y*(1+t^2) = 2*t) :
    point t = (x,y) := by
  apply Prod.ext
  · exact ((eq_div_iff hd).mpr hx).symm
  · exact ((eq_div_iff hd).mpr hy).symm

theorem point0 : point circleFallbackParameter0 = (x0,y0) :=
  point_of_products _ _ _ (outside_has_denominator _ circleFallbackParameter0_im)
    numerator_x0 numerator_y0
theorem point1 : point circleFallbackParameter1 = (x1,y1) :=
  point_of_products _ _ _ (outside_has_denominator _ circleFallbackParameter1_im)
    numerator_x1 numerator_y1

theorem fallback0 : AspisR1CircleFallback.transcript.circle_fallback_point 0#usize =
    .ok (AspisR1CircleFallback.fromR72Point (encodePoint (x0,y0))) := by
  rw [AspisR1CircleFallback.RawCircleFallbackOutputBridge.fallback_zero_output, point0]
theorem fallback1 : AspisR1CircleFallback.transcript.circle_fallback_point 1#usize =
    .ok (AspisR1CircleFallback.fromR72Point (encodePoint (x1,y1))) := by
  rw [AspisR1CircleFallback.RawCircleFallbackOutputBridge.fallback_one_output, point1]

-- The model's mapper reaches the error arm on the canonical zero parameter.
theorem zero_mapper : AspisR72Sampler.circle.secure_ood_circle_point_from_parameter
    (encode 0) = .ok (.Err .ParameterInCm31Subfield) := by
  apply ood_subfield
  · simp
  · rfl

#print axioms numerator_x0
#print axioms numerator_y0
#print axioms numerator_x1
#print axioms numerator_y1
#print axioms point0
#print axioms point1
#print axioms fallback0
#print axioms fallback1
#print axioms zero_mapper
end CDX.Fallback
