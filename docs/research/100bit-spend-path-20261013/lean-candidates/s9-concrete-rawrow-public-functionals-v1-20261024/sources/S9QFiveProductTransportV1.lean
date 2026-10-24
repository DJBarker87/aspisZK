import AspisV8R15.ExactTowerBase
import S9QuadraticFieldMulProjectionV1
set_option autoImplicit false
noncomputable section
namespace AspisR1S9QFiveProductTransportV1
open AspisR1S9QuadraticFieldMulProjectionV1 (projectedMul)
open AspisV8R15.ExactTowerBase
abbrev Q := QM31Exact
noncomputable def fieldFive {K : Type} [Field K] (a b c d e : K) : K :=
  projectedMul (projectedMul a b) (projectedMul (projectedMul c d) e)

theorem generic_five_projected {K : Type} [Field K] (a b c d e : K) :
    (a*b)*((c*d)*e)=fieldFive a b c d e := rfl

/-- Reuse the existing generic quadratic Field projection proof on the
actual quartic carrier, keeping every operand opaque. -/
theorem q_mul_projected (a b : Q) : a*b=projectedMul a b :=
  (AspisR1S9QuadraticFieldMulProjectionV1.quadratic_field_mul
    (K:=CM31Exact) qm31R 0 a b).symm

theorem q_five_projected (a b c d e : Q) :
    (a*b)*((c*d)*e)=fieldFive a b c d e := by
  have hab := q_mul_projected a b
  have hcd := q_mul_projected c d
  have hcde := (q_mul_projected (c*d) e).trans
    (congrArg (fun t : Q => projectedMul t e) hcd)
  exact (q_mul_projected (a*b) ((c*d)*e)).trans
    (congrArg₂ (fun x y : Q => projectedMul x y) hab hcde)

#print axioms generic_five_projected
#print axioms q_mul_projected
#print axioms q_five_projected
end AspisR1S9QFiveProductTransportV1
end
