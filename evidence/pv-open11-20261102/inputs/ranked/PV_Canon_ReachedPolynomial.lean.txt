import R1Z.PV_Canon_Deployment
import R1Z.PV_Canon_HornerObligation
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
/-- Composition of the two explicit remaining source/deployment obligations.
The proved local domain invariant supplies the row's canonical preconditions. -/
theorem reached_polynomial (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    (reached : Array aspis_core.field.QM31 28#usize → aspis_core.field.QM31 → Prop)
    (binding : P_NativePrefixBinding base ops reached)
    (shipped : Evaluator) (source : P_op121 shipped) :
    ∀ p q, reached p q → ∃ z, shipped p q = .ok z ∧ Q z ∧
      decodeQ z=polynomialValue (decodeQ q) p.val := by
  intro p q h
  obtain ⟨hp,hq⟩ := reached_canonical base ops reached binding p q h
  exact op121_polynomial_of_source_law shipped source p q hp hq
#print axioms reached_polynomial
end R1Z.PV_Canon
