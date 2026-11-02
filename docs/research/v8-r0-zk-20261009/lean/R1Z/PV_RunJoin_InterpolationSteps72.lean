import R1Z.PV_RunJoin_InterpolationCongruence72
set_option autoImplicit false
namespace R1Z.PV_RunJoin_InterpolationSteps72
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

theorem complete (a b : ExternalFuns) (h55 : a.op55=b.op55)
    (h57 : a.op57=b.op57) (h74 : a.op74=b.op74) :
    @host_sumcheck.interpolation_basis_steps _ a=@host_sumcheck.interpolation_basis_steps _ b := by
  delta host_sumcheck.interpolation_basis_steps
  delta host_sumcheck.interpolation_basis_steps.mutual
  rw [PV_RunJoin_InterpolationCongruence72.extend a b h55 h57 h74]
  simp only [aspis_core.field.M31.mul,aspis_core.field.M31.sub,h57,h74]

#print axioms complete
end R1Z.PV_RunJoin_InterpolationSteps72
