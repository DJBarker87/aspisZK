import R1Z.ProverRwSuccessWireSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessWireInstall
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
-- The retained private-leaf-salts domain. This is not a feature-agnostic pin.
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessEquality.selected ops with op260 := .ok ProverRwSuccessWireSource.r1_wire.DOMAIN}
theorem domain_source (ops : ExternalFuns) :
    (selected ops).op260 = .ok ProverRwSuccessWireSource.r1_wire.DOMAIN := rfl
theorem domain_length : Slice.len ProverRwSuccessWireSource.r1_wire.DOMAIN=38#usize := rfl
#print axioms domain_source
#print axioms domain_length
end R1Z.ProverRwSuccessWireInstall
