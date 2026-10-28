import R1Z.ProverRwP6FlatSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwP6FlatInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwP6TransitionInstall.selected ops with op51 := ProverRwP6FlatSource.wide_bytes_flat}
theorem source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op51 x = ProverRwP6FlatSource.wide_bytes_flat x := rfl
theorem transition_preserved (ops : ExternalFuns)
    (p : ProverRwP6TransitionTransport.Public) :
    (selected ops).op225 p = ProverRwP6TransitionTransport.transition p := rfl
#print axioms source
#print axioms transition_preserved
end R1Z.ProverRwP6FlatInstall
