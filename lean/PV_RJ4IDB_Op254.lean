import PV_RJ4IDB_PowersBridge
import R1Z.ProverRwP6PowersInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJ4IDB_Op254
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev W := aspis_core.field.wide_exact.WideExact

/-- The static prover-local indexed powers body interpreted with the same
primitive dictionary captured by runjoin's retained powers installation. -/
def callback (ops : ExternalFuns) (N : Usize) (x : W) : Result (Array W N) :=
  @PV_RJ4IDB_PowersControl.powers _ (ProverRwP6BoundaryInstall.selected ops) N x

theorem entry (ops : ExternalFuns) (N : Usize) (x : W) :
    callback ops N x = ProverRwP6PowersInstall.powers ops N x :=
  @PV_RJ4IDB_PowersBridge.complete _ (ProverRwP6BoundaryInstall.selected ops) N x

/-- Same incoming dictionary as GammaPowers44.inputs, using the modeled
indexed source body instead of the retained early-return body. -/
def incoming (ops : ExternalFuns) : ExternalFuns :=
  {ops with op254 := callback ops}

theorem installation (ops : ExternalFuns) :
    incoming ops = {ops with op254 := ProverRwP6PowersInstall.powers ops} := by
  have same : callback ops = ProverRwP6PowersInstall.powers ops := by
    funext N x
    exact entry ops N x
  unfold incoming
  rw [same]

#print axioms entry
#print axioms installation
end R1Z.PV_RJ4IDB_Op254
