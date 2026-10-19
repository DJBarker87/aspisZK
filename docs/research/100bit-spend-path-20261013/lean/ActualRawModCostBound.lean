import ActualScaledDivisorMonic
import ActualRawModRemainderSizeBound

/-! Polynomial coefficient-operation bound for the exact retained raw `%`
mirror, including its normalization products. Tree-format independent. -/
set_option autoImplicit false
namespace ActualRawModCostBound
open CompPoly ActualRawModRemainderCostBridge ActualScaledDivisorMonic
open ActualRawPowCoefficientBudget
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

theorem division_cost_models_eq (fuel : Nat) (p q : CPolynomial.Raw F) :
    ActualRawLongDivisionCost.divModByMonicAuxWithCost fuel p q =
      ActualRawLongDivisionCostV2.divModByMonicAuxWithCost fuel p q := by
  induction fuel generalizing p with
  | zero => simp only [ActualRawLongDivisionCost.divModByMonicAuxWithCost,
      ActualRawLongDivisionCostV2.divModByMonicAuxWithCost]
  | succ fuel ih =>
    unfold ActualRawLongDivisionCost.divModByMonicAuxWithCost
      ActualRawLongDivisionCostV2.divModByMonicAuxWithCost
    split
    · rfl
    · dsimp only
      rw [ih]
      rfl

theorem constant_mul_budget (a : F) (p : CPolynomial.Raw F) :
    rawMulCoefficientBudget (CPolynomial.Raw.C a) p = 3*p.size+2 := by
  have hc : (CPolynomial.Raw.C a : CPolynomial.Raw F).size = 1 := rfl
  simp only [rawMulCoefficientBudget,hc,Nat.one_mul]
  omega

def modBudget (N : Nat) : Nat := 6*N+5 + N*(100*(N+4)*(N+4))

theorem raw_mod_cost_le (p q : CPolynomial.Raw F) (N : Nat)
    (hq : q.trim = q) (hq0 : q ≠ (0 : CPolynomial.Raw F))
    (hpN : p.size ≤ N) (hqN : q.size ≤ N) :
    (rawModWithCost p q).2 ≤ modBudget N := by
  have ha := ActualRawModRemainderSizeBound.scaledDividend_size_le p q
  have hdiv := ActualLongDivisionTotalCostV1.total_cost_le_fuel_mul
    (scaledDividend p q).size (N+1) (scaledDividend p q) (monicScaledDivisor q)
    (scaled_dividend_trim p q) (scaled_divisor_trim q)
    (scaled_divisor_leadingCoeff q hq hq0) (scaled_divisor_positive q hq hq0)
    (by omega) (by omega)
  have hdivN : (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost
      (scaledDividend p q).size (scaledDividend p q) (monicScaledDivisor q)).2 ≤
      N*(100*(N+4)*(N+4)) := by
    exact hdiv.trans (by
      simpa only [Nat.add_assoc] using
        Nat.mul_le_mul_right (100*(N+4)*(N+4)) (ha.trans hpN))
  unfold rawModWithCost
  dsimp only
  rw [constant_mul_budget,constant_mul_budget,division_cost_models_eq]
  unfold modBudget
  omega

#print axioms division_cost_models_eq
#print axioms constant_mul_budget
#print axioms raw_mod_cost_le
end ActualRawModCostBound
