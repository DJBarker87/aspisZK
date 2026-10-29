import PV_RJ4IDB_PowersSafety
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_PowersTotal
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
variable [ExternalTypes]
theorem complete (ops : ExternalFuns) (N : Usize) (x : W) :
 ∃ out, PV_RJ4IDB_NativePowers.callback ops N x = ok out := by
 unfold PV_RJ4IDB_NativePowers.callback
 rw [PV_RJ4IDB_PowersControl.source]
 letI : ExternalFuns := PV_RJ4IDB_NativePowers.primitives ops
 have hz : aspis_core.field.wide_exact.WideExact.ZERO = ok
  (ProverRwP6PowersNativeFactor.zero) := rfl
 have ho : ProverRwP6PowersSource.aspis_core.field.wide_exact.WideExact.ONE = ok
  (ProverRwP6PowersNativeFactor.one) := rfl
 simp only [hz,ho,bind_tc_ok]
 exact PV_RJ4IDB_PowersSafety.finite_total ops x N.val _ _ 0#usize (by change 0+_= _; omega)

theorem no_fail (ops : ExternalFuns) (N : Usize) (x : W) (e : Error) :
 PV_RJ4IDB_NativePowers.callback ops N x ≠ .fail e := by
 obtain ⟨out,hout⟩ := complete ops N x
 rw [hout]
 intro h
 cases h

theorem no_diverge (ops : ExternalFuns) (N : Usize) (x : W) :
 PV_RJ4IDB_NativePowers.callback ops N x ≠ .div := by
 obtain ⟨out,hout⟩ := complete ops N x
 rw [hout]
 intro h
 cases h
#print axioms complete
#print axioms no_fail
#print axioms no_diverge
end R1Z.PV_RJ4IDB_PowersTotal
