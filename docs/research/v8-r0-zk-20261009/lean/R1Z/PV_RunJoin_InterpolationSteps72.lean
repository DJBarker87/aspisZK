import R1Z.PV_RunJoin_InterpolationCongruence72
set_option autoImplicit false
namespace R1Z.PV_RunJoin_InterpolationSteps72
open Aeneas Aeneas.Std Result ProverRwFull
universe u

theorem fix_congr {α : Sort u} [Lean.Order.CCPO α] {f g : α → α}
    (hf : Lean.Order.monotone f) (hg : Lean.Order.monotone g) (same : f=g) :
    Lean.Order.fix f hf=Lean.Order.fix g hg := by
  cases same
  rfl

#print axioms fix_congr

variable [ExternalTypes]

theorem complete (a b : ExternalFuns) (h55 : a.op55=b.op55)
    (h57 : a.op57=b.op57) (h74 : a.op74=b.op74) :
    @host_sumcheck.interpolation_basis_steps _ a=@host_sumcheck.interpolation_basis_steps _ b := by
  funext basis denominator degree i
  delta host_sumcheck.interpolation_basis_steps host_sumcheck.interpolation_basis_steps.mutual
  apply congrArg (fun recurse => recurse basis denominator degree)
  apply fix_congr
  funext recurse cells den deg j
  rw [PV_RunJoin_InterpolationCongruence72.extend a b h55 h57 h74]
  simp only [aspis_core.field.M31.mul,aspis_core.field.M31.sub,h57,h74]

#print axioms complete
end R1Z.PV_RunJoin_InterpolationSteps72
