import RawExtractorFixedProtocolPolynomial

/-! Explicit linear numerical envelope for fixed protocol parameters.
The implementation ledger remains an independent obligation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawExtractorFixedProtocolEnvelope
open RawExtractorCostComposedV2 RawExtractorFixedProtocolPolynomial

def slope (p : Parameters) : Nat :=
  (p.overheadConstant + 7 * p.n) +
    (2 * p.overheadConstant + 7 * p.n) * (p.b + 1)^2

def intercept (p : Parameters) : Nat :=
  let E := p.n + p.listSize + p.b + 1
  arithmeticConstant p + p.overheadConstant * E +
    (arithmeticConstant p + 2 * p.overheadConstant * E) * (p.b + 1)^2

theorem affine_budget (p : Parameters) (Q : Nat) :
    (family p Q).attemptBudget = slope p * (Q + 1161) + intercept p := by
  rw [← budget_eval]
  simp only [budgetPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, slope, intercept]
  ring

def constant (p : Parameters) : Nat := slope p + intercept p

theorem linear_envelope (p : Parameters) (Q : Nat) :
    (family p Q).attemptBudget ≤ constant p * (Q + 1161) := by
  rw [affine_budget]
  have hi : intercept p ≤ intercept p * (Q + 1161) := by
    have h : 1 ≤ Q + 1161 := by omega
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (intercept p) h
  unfold constant
  rw [Nat.add_mul]
  exact Nat.add_le_add_left hi _

/-- The total implementation claim is conditional on its real ledger. The
fixed family has no remaining coordinate-bound premise, and every private
tape (including aborts) is covered by the existing ledger consumer. -/
theorem accepted_linear_cost
    (implementation : Nat → RawExtractorCostComposedBin.CostedExtractor)
    (p : Parameters)
    (ledger : ∀ Q, RawExtractorCostComposedBin.LedgerRefinement
      (implementation Q) (family p Q) Q)
    (Q : Nat) (run : RawCutProverCompiler.RunView)
    (ha : run.2.2 = true) (hlog : run.1.length ≤ Q + 1161) :
    AspisV8R19.OracleResampling.mean
      (fun coins : RawExtractorCostComposedV2.Coins =>
        (((implementation Q).eval run coins).2.total : ℚ)) ≤
      (Nat.cast (constant p * (Q + 1161)) : ℚ) := by
  have hc := (RawExtractorCostComposedBin.accepted_attempt_cost
    (implementation Q) (family p Q) Q (ledger Q) run ha hlog).2
  exact hc.trans (by exact_mod_cast linear_envelope p Q)

#print axioms affine_budget
#print axioms linear_envelope
#print axioms accepted_linear_cost
end AspisR1.RawExtractorFixedProtocolEnvelope
end
