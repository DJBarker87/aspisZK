import R1Z.PV_Canon_HornerMeaning
import R1Z.PV_Canon_RowObligation
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
 def hornerEvaluator : Evaluator := fun p q => horner q p.val
/-- The exact remaining canonical source law for a Horner route. This Prop
has no proof supplied here: the shipped association is open. -/
def P_op121 (shipped : Evaluator) : Prop := CanonicalOp121Law shipped hornerEvaluator
 theorem op121_polynomial_of_source_law (shipped : Evaluator) (law : P_op121 shipped)
    (p : Array aspis_core.field.QM31 28#usize) (q : aspis_core.field.QM31)
    (hp : Coeffs p) (hq : Q q) :
    ∃ z, shipped p q = .ok z ∧ Q z ∧ decodeQ z=polynomialValue (decodeQ q) p.val := by
  obtain ⟨z,hz,hc,hv⟩ := horner_meaning q hq p.val hp
  exact ⟨z,(law p q hp hq).trans hz,hc,hv⟩
#print axioms op121_polynomial_of_source_law
end R1Z.PV_Canon
