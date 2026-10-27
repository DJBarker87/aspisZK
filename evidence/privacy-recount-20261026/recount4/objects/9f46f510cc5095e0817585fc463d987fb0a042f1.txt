import R1Z.PV_Join_GInterpolateCanonical5
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_CurrentPolynomialCanonical5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5 PV_Join_ResultInvariant5

theorem polynomial (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    (values : Array aspis_core.field.QM31 28#usize) :
    Safe QArray (@host_sumcheck.interpolate (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) values) :=
  @PV_Join_GInterpolateCanonical5.interpolate (PV_Join_PublicCaller.native base)
    (PV_Join_PublicCaller.selected base ops) (PV_Join_CanonicalPrimitives5.caller base ops) values

#print axioms polynomial
end R1Z.PV_Join_CurrentPolynomialCanonical5
