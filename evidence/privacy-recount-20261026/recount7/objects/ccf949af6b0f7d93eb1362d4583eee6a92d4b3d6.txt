import R1Z.ProverRwP6PowersFinite
import R1Z.ProverRwP6PowersCongruence
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6PowersInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
-- Capture the existing primitive dictionary before replacing the owner entry.
def powers (ops : ExternalFuns) (N : Usize) (x : aspis_core.field.wide_exact.WideExact) :=
  @ProverRwP6PowersSource.weights.powers _ (ProverRwP6BoundaryInstall.selected ops) N x
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwP6BoundaryInstall.selected ops with op254 := powers ops}
theorem source (ops : ExternalFuns) (N : Usize) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op254 N x = powers ops N x := rfl
theorem old_callback_removed (ops : ExternalFuns)
    (callback : (N : Usize) → aspis_core.field.wide_exact.WideExact → Result (Array aspis_core.field.wide_exact.WideExact N))
    (N : Usize) (x : aspis_core.field.wide_exact.WideExact) :
    (selected {ops with op254 := callback}).op254 N x = (selected ops).op254 N x := by
  exact ProverRwP6PowersCongruence.powers
    (ProverRwP6BoundaryInstall.selected {ops with op254 := callback})
    (ProverRwP6BoundaryInstall.selected ops) N x rfl rfl (fun _ _ => rfl)
-- The captured primitive dictionary is explicit; this theorem asserts no native
-- field adequacy or equality to the security model.
#print axioms source
#print axioms old_callback_removed
end R1Z.ProverRwP6PowersInstall
