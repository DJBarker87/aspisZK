import R1Z.PrivacyR1HeadlineV2Sim
import R1Z.SimCostView
import R1Z.SimCostSampling
import R1Z.SimCostObstruction

/-! One final additive import packet, not a frozen-manifest replay. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostPacket
open Polynomial

def costPolynomial (C L T : Nat) : Polynomial Nat :=
  Polynomial.C (SimCostIdeal.coefficient C L T) * (X+1)

theorem polynomial_eval (C L T q : Nat) :
    (costPolynomial C L T).eval q = SimCostIdeal.coefficient C L T*(q+1) := by
  simp [costPolynomial]

theorem polynomial_degree (C L T : Nat) : (costPolynomial C L T).natDegree ≤ 1 := by
  have h := @Polynomial.natDegree_mul_le Nat _
    (Polynomial.C (SimCostIdeal.coefficient C L T)) (X+1)
  have ha := Polynomial.natDegree_add_le (X : Polynomial Nat) 1
  simp only [Polynomial.natDegree_C, Polynomial.natDegree_X,
    Polynomial.natDegree_one, max_eq_left (show 0 ≤ 1 by omega), zero_add] at h ha
  exact h.trans ha

#print axioms polynomial_eval
#print axioms polynomial_degree
end R1Z.SimCostPacket
