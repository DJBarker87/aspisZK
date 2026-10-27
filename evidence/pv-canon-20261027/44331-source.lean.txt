import R1Z.PV_Canon_HornerObligation
import R1Z.PV_Canon_QInjective
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
/-- Equivalent explicit proof target: total success, canonical output, and
polynomial meaning on the canonical input domain. Still a P obligation. -/
def PolynomialLaw (shipped : Evaluator) : Prop :=
  ∀ p q, Coeffs p → Q q → ∃ z, shipped p q = .ok z ∧ Q z ∧
    decodeQ z=polynomialValue (decodeQ q) p.val
 theorem op121_law_iff (shipped : Evaluator) : P_op121 shipped ↔ PolynomialLaw shipped := by
  constructor
  · intro h p q hp hq
    exact op121_polynomial_of_source_law shipped h p q hp hq
  · intro h p q hp hq
    obtain ⟨z,hz,hcz,hvz⟩ := h p q hp hq
    obtain ⟨w,hw,hcw,hvw⟩ := horner_meaning q hq p.val hp
    have same : z=w := canonical_qinjective z w hcz hcw (hvz.trans hvw.symm)
    change shipped p q = horner q p.val
    rw [hz,hw,same]
#print axioms op121_law_iff
end R1Z.PV_Canon
