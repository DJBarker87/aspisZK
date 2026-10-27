import R1Z.ProverRwP6PowersSelectedTotal
import R1Z.ProverRwP6PowersRunTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersTotal
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6PowersControl
variable [ExternalTypes]
theorem total (ops : ExternalFuns) (N : Usize) (x : W) :
    ∃ result, (ProverRwP6PowersInstall.selected ops).op254 N x = ok result := by
  letI : ExternalFuns := ProverRwP6BoundaryInstall.selected ops
  obtain ⟨zero,hz⟩ := ProverRwP6PowersSelectedTotal.zero ops
  obtain ⟨one,ho⟩ := ProverRwP6PowersSelectedTotal.one ops
  obtain ⟨result,hr⟩ := ProverRwP6PowersRunTotal.finite_total x N.val
    (Array.repeat N zero) one 0#usize (by change 0+_= _; omega)
    (fun a b => ProverRwP6PowersSelectedTotal.mul ops a b)
  have hl := (ProverRwP6PowersFinite.loop_finite x N.val
    (Array.repeat N zero) one 0#usize (by change 0+_= _; omega)).trans hr
  change ∃ result, ProverRwP6PowersSource.weights.powers N x = ok result
  rcases result with ⟨out,pending⟩
  cases pending <;>
    simp only [ProverRwP6PowersSource.weights.powers,
      ProverRwP6PowersSource.aspis_core.field.wide_exact.WideExact.ONE,
      ProverRwFull.aspis_core.field.wide_exact.WideExact.ZERO,
      ProverRwFull.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.ONE,
      hz,ho,hl,bind_tc_ok] <;> exact ⟨_,rfl⟩
#print axioms total
end R1Z.ProverRwP6PowersTotal
