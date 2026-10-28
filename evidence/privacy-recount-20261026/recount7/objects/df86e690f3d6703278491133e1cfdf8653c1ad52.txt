import R1Z.ProverRwP6PowersNativeBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersNativeFactor
open Aeneas Aeneas.Std Result ProverRwFull ProverRwP6PowersNativeStep
open ProverRwP6PowersFinite
variable [ExternalTypes]
abbrev zero : W := fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO
abbrev one : W := fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE

theorem factor (ops : ExternalFuns) (N : Usize) (x : W) :
    letI : ExternalFuns := dict ops
    ProverRwP6PowersInstall.powers ops N x =
      ProverRwP6ResultMap.map finish (finite x N.val (Array.repeat N zero) one 0#usize) := by
  letI : ExternalFuns := dict ops
  have hz : aspis_core.field.wide_exact.WideExact.ZERO = ok zero := rfl
  have ho : ProverRwP6PowersSource.aspis_core.field.wide_exact.WideExact.ONE = ok one := rfl
  apply (ProverRwP6PowersFinite.powers_finite N x).trans
  simp only [hz,ho,bind_tc_ok]
  cases hr : finite x N.val (Array.repeat N zero) one 0#usize with
  | fail e => rfl
  | div => rfl
  | ok r =>
    rcases r with ⟨out,pending⟩
    cases pending <;> rfl

#print axioms factor
end R1Z.ProverRwP6PowersNativeFactor
