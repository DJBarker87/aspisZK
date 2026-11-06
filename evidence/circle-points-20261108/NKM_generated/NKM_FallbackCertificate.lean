import AspisV8R19.SamplerClosureCircleSourceExecution
import R0P.CircleSampler
set_option autoImplicit false
noncomputable section
namespace NKM_FallbackCertificate
open AspisV8R15.ExactTowerBase
open R0P.SemSource

def inverse0 : QM31Exact := ⟨⟨3 / 10, -(1 / 10)⟩, 0⟩
def inverse1 : QM31Exact := ⟨⟨32 / 65, -(9 / 65)⟩, ⟨-(14 / 65), 8 / 65⟩⟩

theorem certificate0 : (1 + circleFallbackParameter0 * circleFallbackParameter0) * inverse0 = 1 := by
 have h10 : (10 : M31Exact) ≠ 0 := by decide
 have h65 : (65 : M31Exact) ≠ 0 := by decide
 ext <;> norm_num [circleFallbackParameter0, inverse0, qm31R,
  QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
  QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, show (2 : CM31Exact) = ⟨2,0⟩ from rfl, P] <;>
  field_simp [h10,h65] <;>
  norm_num [show (2 : CM31Exact).re = 2 from rfl, show (2 : CM31Exact).im = 0 from rfl, h10,h65,P]

theorem certificate1 : (1 + circleFallbackParameter1 * circleFallbackParameter1) * inverse1 = 1 := by
 have h10 : (10 : M31Exact) ≠ 0 := by decide
 have h65 : (65 : M31Exact) ≠ 0 := by decide
 ext <;> norm_num [circleFallbackParameter1, inverse1, qm31R,
  QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
  QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast, show (2 : CM31Exact) = ⟨2,0⟩ from rfl, P] <;>
  field_simp [h10,h65] <;>
  norm_num [show (2 : CM31Exact).re = 2 from rfl, show (2 : CM31Exact).im = 0 from rfl, h10,h65,P]

theorem denominator0 : 1 + circleFallbackParameter0 * circleFallbackParameter0 ≠ 0 := by
 intro h
 have hc := certificate0
 rw [h, zero_mul] at hc
 exact zero_ne_one hc

theorem denominator1 : 1 + circleFallbackParameter1 * circleFallbackParameter1 ≠ 0 := by
 intro h
 have hc := certificate1
 rw [h, zero_mul] at hc
 exact zero_ne_one hc

#print axioms certificate0
#print axioms certificate1
#print axioms denominator0
#print axioms denominator1
end NKM_FallbackCertificate
end
