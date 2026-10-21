import R1Z.PrivacyR1HeadlineV2SimProto
import R1Z.SimCostLazyProtocol
import R1Z.SimCostTapeCoupling
import R1Z.SimCostRelativeObstruction

/-! Final focused additive packet. This imports the relative headline, exact
lazy ROM law, actual-tape binary coupling and compiled metadata obstruction.
It is not an unconditional implementation certificate or a release manifest. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostRelativePacket
attribute [local instance] Classical.propDecidable
open Polynomial R0Z.FsAbortBounds R1Z.SimCostBinaryCoupling R1Z.SimCostTapeCoupling

def costPolynomial (C L T : Nat) : Polynomial Nat :=
  Polynomial.C (SimCostRelativeIdeal.relativeCoefficient C L T) * (X+1)

theorem polynomial_eval (C L T n : Nat) :
    (costPolynomial C L T).eval n = SimCostRelativeIdeal.relativeCoefficient C L T*(n+1)^1 := by
  simp only [costPolynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, pow_one]

theorem polynomial_degree (C L T : Nat) : (costPolynomial C L T).natDegree ≤ 1 := by
  have h := @Polynomial.natDegree_mul_le Nat _
    (Polynomial.C (SimCostRelativeIdeal.relativeCoefficient C L T)) (X+1)
  have ha := Polynomial.natDegree_add_le (X : Polynomial Nat) 1
  simp only [Polynomial.natDegree_C, Polynomial.natDegree_X,
    Polynomial.natDegree_one, max_eq_left (show 0 ≤ 1 by omega), zero_add] at h ha
  exact h.trans ha

/-- Actual protocol-tape failure mass, not a conjectured sample count or
assumed geometric source. The numeric-envelope premise is kept explicit. -/
theorem protocol_tape_total_error (epsilon : ℚ)
    (he : epsilon ≤ 1/(2:ℚ)^109 + 1/(2:ℚ)^137 + 1/(2:ℚ)^454 +
      128*((2:ℚ)^25+1)/(2:ℚ)^190) :
    epsilon + mass (bad 8 (Fintype.card Coordinates)) < 1/(2:ℚ)^100 :=
  total_source_error epsilon he _ sample_count_small

#print axioms polynomial_eval
#print axioms polynomial_degree
#print axioms protocol_tape_total_error
end R1Z.SimCostRelativePacket
