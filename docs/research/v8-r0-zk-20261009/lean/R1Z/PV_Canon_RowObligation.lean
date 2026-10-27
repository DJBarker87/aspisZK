import R1Z.PV_Canon_Carrier
set_option autoImplicit false
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std ProverRwFull
abbrev Evaluator := Array aspis_core.field.QM31 28#usize → aspis_core.field.QM31 → Result aspis_core.field.QM31
/-- An outstanding P source obligation. This definition is not a proof of the
shipped/reference equality and introduces no accepted trust item. -/
def CanonicalOp121Law (shipped reference : Evaluator) : Prop :=
  ∀ polynomial challenge, Coeffs polynomial → Q challenge →
    shipped polynomial challenge = reference polynomial challenge
 theorem source_law_at_canonical_call (shipped reference : Evaluator)
    (law : CanonicalOp121Law shipped reference)
    (polynomial : Array aspis_core.field.QM31 28#usize)
    (challenge : aspis_core.field.QM31) (hp : Coeffs polynomial) (hq : Q challenge) :
    shipped polynomial challenge = reference polynomial challenge :=
  law polynomial challenge hp hq
#print axioms source_law_at_canonical_call
end R1Z.PV_Canon
