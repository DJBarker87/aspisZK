import RawExtractorParameterPolynomial
import RawRecordedPublicSpendExtractorCompletenessBin

/-! M10 statement fix: every ledger obligation is restricted to the actual
log-length domain. These adequacy fields still require implementation proofs;
output equality or a choice of resource labels does not establish them. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawExtractorCostComposedBin
open FS
open RawCutProverCompiler RawExtractorCostComposedV2 RawExtractorCostLedger
open AspisV8R19.OracleResampling

structure CostedExtractor where
  eval : RunView → Coins → Option SpendRelation.Wspend × Resources
  value : ∀ run coins, (eval run coins).1 =
    RawRecordedPublicSpendExtractorBin.extract run coins

/-- Missing implementation-level premises, deliberately exposed for C3.
`jobs` must enumerate every arithmetic call, including failed retries.
`bounded_jobs` must cover normalization, interpolation, list filters,
merge, final witness checking, sampler, and modular-multiplication work.
`reads` must link actual recorded-log reconstruction to the finite-log model.
`bit_accounting` must cover all allocation, parsing and arithmetic bit work.
These premises assert adequacy of the cost model, beyond value refinement. -/
structure LedgerRefinement (e : CostedExtractor) (p : Parameters) (Q : Nat) : Prop where
  log_capacity : Q + 1161 ≤ p.logSize
  bounded_jobs : ∀ run coins, run.2.2 = true → run.1.length ≤ Q + 1161 →
    ∃ jobs : Jobs K, jobs.Bounded p.n p.b p.count ∧
      (e.eval run coins).2.fieldOps ≤ jobs.charge p.mulBudget + p.overhead
  reads : ∀ run coins, run.2.2 = true → run.1.length ≤ Q + 1161 →
    (e.eval run coins).2.logReads ≤ p.readBudget
  bit_accounting : ∀ run coins, run.2.2 = true → run.1.length ≤ Q + 1161 →
    (e.eval run coins).2.bits ≤
      ((e.eval run coins).2.fieldOps + (e.eval run coins).2.logReads +
        p.overhead)*(p.b+1)^2

/-- All finite private tapes, including aborts, satisfy a deterministic bound;
therefore their uniform mean does too. No geometric-retry assumption is used. -/
theorem accepted_attempt_cost (e : CostedExtractor) (p : Parameters)
    (Q : Nat) (h : LedgerRefinement e p Q) (run : RunView)
    (ha : run.2.2 = true) (hlog : run.1.length ≤ Q + 1161) :
    (∀ coins, (e.eval run coins).2.total ≤ p.attemptBudget) ∧
    mean (fun coins : Coins => ((e.eval run coins).2.total : ℚ)) ≤
      (p.attemptBudget : ℚ) := by
  have hall (coins : Coins) : (e.eval run coins).2.total ≤ p.attemptBudget := by
    obtain ⟨jobs, hj, hf⟩ := h.bounded_jobs run coins ha hlog
    have hf' : (e.eval run coins).2.fieldOps ≤ p.fieldBudget :=
      hf.trans (Nat.add_le_add_right (jobs_charge_le jobs p.n p.b p.count p.mulBudget hj) _)
    have hr := h.reads run coins ha hlog
    have hb := (h.bit_accounting run coins ha hlog).trans
      (Nat.mul_le_mul_right ((p.b+1)^2)
        (Nat.add_le_add_right (Nat.add_le_add hf' hr) p.overhead))
    exact Nat.add_le_add (Nat.add_le_add hf' hr) hb
  refine ⟨hall, ?_⟩
  calc
    _ ≤ mean (fun _ : Coins => (p.attemptBudget : ℚ)) := mean_mono (by
      intro coins
      exact_mod_cast hall coins)
    _ = _ := mean_const _


/-- Uniform polynomial in Q, with one fixed overhead pair and one fixed
coordinate slack across the entire family. -/
def queryPolynomial (a k c : Nat) : Polynomial Nat :=
  (RawExtractorParameterPolynomial.budgetPolynomial a k).comp
    (Polynomial.X + Polynomial.C c)

theorem queryPolynomial_eval (Q a k c : Nat) :
    (queryPolynomial a k c).eval Q =
      (RawExtractorParameterPolynomial.diagonal (Q + c) a k).attemptBudget := by
  rw [queryPolynomial, Polynomial.eval_comp]
  simpa using RawExtractorParameterPolynomial.budgetPolynomial_eval (Q + c) a k

/-- This is conditional on the real size-restricted resource ledger and
parameter bounds, including rejected/aborting private tapes on accepted runs.
It does not manufacture either implementation premise. -/
theorem accepted_attempt_polynomial (family : Nat → CostedExtractor)
    (params : Nat → Parameters) (a k c : Nat)
    (h_M10_ledger : ∀ Q, LedgerRefinement (family Q) (params Q) Q)
    (h_M10_uniform : ∀ Q, RawExtractorParameterPolynomial.CoordinateBound
      (params Q) (Q + c) a k)
    (Q : Nat) (run : RunView) (ha : run.2.2 = true)
    (hlog : run.1.length ≤ Q + 1161) :
    mean (fun coins : Coins => (((family Q).eval run coins).2.total : ℚ)) ≤
      (Nat.cast ((queryPolynomial a k c).eval Q) : ℚ) := by
  have hc := (accepted_attempt_cost (family Q) (params Q) Q
    (h_M10_ledger Q) run ha hlog).2
  have hp := RawExtractorParameterPolynomial.attemptBudget_le_diagonal
    (params Q) (Q + c) a k (h_M10_uniform Q)
  rw [← queryPolynomial_eval Q a k c] at hp
  exact hc.trans (by exact_mod_cast hp)

#print axioms accepted_attempt_cost
#print axioms queryPolynomial_eval
#print axioms accepted_attempt_polynomial
end AspisR1.RawExtractorCostComposedBin
end
