import Mathlib.Tactic.Ring
/-! Local identity used by the 4-coefficient Horner evaluator. The SIMD/dot
integer reduction contract is the existing core's three-product contract.
No compiler/backend or whole Rust source refinement is asserted. -/
namespace AspisV8.BlockHorner
variable {K : Type*} [CommRing K]
theorem step (a p0 p1 p2 p3 tail : K) :
    (p0 + a*p1 + a^2*p2 + a^3*p3) + a^4*tail =
      p0 + a*(p1 + a*(p2 + a*(p3 + a*tail))) := by ring
#print axioms step
end AspisV8.BlockHorner
