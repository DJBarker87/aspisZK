import R1Z.ProverRwP6BoundaryStep
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6BoundaryInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwP6FlatInstall.selected ops with op120 := ProverRwP6BoundarySource.boundary_flat}
theorem source (ops : ExternalFuns) (p : Array aspis_core.field.QM31 28#usize) :
    (selected ops).op120 p = ProverRwP6BoundarySource.boundary_flat p := rfl
theorem serialization_preserved (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op51 x = ProverRwP6FlatSource.wide_bytes_flat x := rfl
theorem transition_preserved (ops : ExternalFuns) (p : ProverRwP6TransitionTransport.Public) :
    (selected ops).op225 p = ProverRwP6TransitionTransport.transition p := rfl
#print axioms source
#print axioms serialization_preserved
#print axioms transition_preserved
end R1Z.ProverRwP6BoundaryInstall
