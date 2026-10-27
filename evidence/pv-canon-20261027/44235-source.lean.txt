import R1Z.PV_Canon_Carrier
import R1Z.PV_Join_CurrentPolynomialCanonical5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
/-- Canonical interpolation outputs even for arbitrary raw input values.
This statement uses the existing current caller installation explicitly. -/
theorem polynomial (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    (values polynomial : Array aspis_core.field.QM31 28#usize)
    (h : @host_sumcheck.interpolate (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) values = .ok polynomial) : Coeffs polynomial :=
  PV_Join_CurrentPolynomialCanonical5.polynomial base ops values polynomial h
#print axioms polynomial
end R1Z.PV_Canon
