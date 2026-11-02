import R1Z.PV_RunJoin_InterpolationSteps72
set_option autoImplicit false
namespace R1Z.PV_RunJoin_InterpolationDictionary72
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] (a b : ExternalFuns)

theorem basis (h55 : a.op55=b.op55) (h56 : a.op56=b.op56)
    (h57 : a.op57=b.op57) (h74 : a.op74=b.op74) :
    @host_sumcheck.interpolation_basis _ a=@host_sumcheck.interpolation_basis _ b := by
  unfold host_sumcheck.interpolation_basis
  rw [PV_RunJoin_InterpolationSteps72.complete a b h55 h57 h74]
  simp only [aspis_core.field.M31.ZERO,aspis_core.field.M31.ONE,h55,h56]

theorem complete (h55 : a.op55=b.op55) (h56 : a.op56=b.op56)
    (h57 : a.op57=b.op57) (h59 : a.op59=b.op59) (h64 : a.op64=b.op64)
    (h67 : a.op67=b.op67) (h70 : a.op70=b.op70) (h74 : a.op74=b.op74) :
    @host_sumcheck.interpolate _ a=@host_sumcheck.interpolate _ b := by
  unfold host_sumcheck.interpolate host_sumcheck.interpolate_loop host_sumcheck.interpolate_loop.body
  rw [basis a b h55 h56 h57 h74,PV_RunJoin_InterpolationCongruence72.accumulate a b h67 h70]
  simp only [aspis_core.field.QM31.ZERO,aspis_core.field.M31.inv,aspis_core.field.QM31.mul_m31,h64,h59,h70]

#print axioms basis
#print axioms complete
end R1Z.PV_RunJoin_InterpolationDictionary72
