import AspisV8R19.R728BalancedImageTails
import AspisV8R19.SamplerCirclePolicy

set_option autoImplicit false
namespace AspisV8R19.R729SelectedCircleTailBoundary
open AspisV8R17 AspisV8R16 AspisR19
open AspisV8R15.ExactTowerBase
open R728BalancedImageTails
open scoped BigOperators
noncomputable section

lemma selected_circle_norm_ne_zero (u v : QM31Exact)
    (hu : u.im ≠ 0) (hv : v.im ≠ 0) :
    (u * v - 1)^2 + (-(u + v))^2 ≠ 0 := by
  apply circle_norm_ne_zero u v
  · exact SamplerCirclePolicy.outside_has_denominator u hu
  · exact SamplerCirclePolicy.outside_has_denominator v hv

lemma selected_balanced_image_tails
    (half alpha u v : QM31Exact) (q : Index 256 → QM31Exact)
    (hu : u.im ≠ 0) (hv : v.im ≠ 0)
    (h23 : flattenFull q 1023 = 0)
    (himage : (u * v - 1) * flattenFull q 1022 - (-(u + v)) * flattenFull q 1021 = 0)
    (hbalance : (∑ r ∈ TwoSwapSourceTable.inactive,
      indexedMask half (1 + u * v) (u * v - 1) (-(u + v)) q r) = 0)
    (hfold : R370KernelEvaluation.firstFold 256 alpha q 255 = 0) :
    flattenFull q 1020 = 0 ∧ flattenFull q 1021 = 0 ∧
      flattenFull q 1022 = 0 ∧ flattenFull q 1023 = 0 := by
  exact balanced_image_tails half (1 + u * v) (u * v - 1) (-(u + v)) alpha q h23 himage hbalance
    (selected_circle_norm_ne_zero u v hu hv) hfold

#print axioms selected_circle_norm_ne_zero
#print axioms selected_balanced_image_tails
end
end AspisV8R19.R729SelectedCircleTailBoundary
