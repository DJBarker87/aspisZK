import R1Z.ProverRwFullFuns
set_option autoImplicit false
namespace R1Z.PV_RunJoin_InterpolationCongruence72
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] (a b : ExternalFuns)

theorem shift (h55 : a.op55=b.op55) :
    @host_sumcheck.interpolation_shift _ a=@host_sumcheck.interpolation_shift _ b := by
  unfold host_sumcheck.interpolation_shift
  simp only [aspis_core.field.M31.ZERO,h55]

theorem cell (h55 : a.op55=b.op55) (h57 : a.op57=b.op57) (h74 : a.op74=b.op74) :
    @host_sumcheck.interpolation_basis_cell _ a=@host_sumcheck.interpolation_basis_cell _ b := by
  unfold host_sumcheck.interpolation_basis_cell
  rw [shift a b h55]
  simp only [aspis_core.field.M31.mul,aspis_core.field.M31.sub,h57,h74]

theorem extend_loop (h55 : a.op55=b.op55) (h57 : a.op57=b.op57) (h74 : a.op74=b.op74) :
    @host_sumcheck.interpolation_extend_loop _ a=@host_sumcheck.interpolation_extend_loop _ b := by
  unfold host_sumcheck.interpolation_extend_loop host_sumcheck.interpolation_extend_loop.body
  rw [cell a b h55 h57 h74]

theorem extend (h55 : a.op55=b.op55) (h57 : a.op57=b.op57) (h74 : a.op74=b.op74) :
    @host_sumcheck.interpolation_extend _ a=@host_sumcheck.interpolation_extend _ b := by
  unfold host_sumcheck.interpolation_extend
  rw [extend_loop a b h55 h57 h74]

theorem accumulate (h67 : a.op67=b.op67) (h70 : a.op70=b.op70) :
    @host_sumcheck.interpolation_accumulate _ a=@host_sumcheck.interpolation_accumulate _ b := by
  unfold host_sumcheck.interpolation_accumulate host_sumcheck.interpolation_accumulate_loop
    host_sumcheck.interpolation_accumulate_loop.body
  simp only [aspis_core.field.QM31.mul_m31,aspis_core.field.QM31.add,h67,h70]

#print axioms shift
#print axioms cell
#print axioms extend_loop
#print axioms extend
#print axioms accumulate
end R1Z.PV_RunJoin_InterpolationCongruence72
