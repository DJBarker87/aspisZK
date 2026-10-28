import R1Z.PV_CB_Phi
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Merkle
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {PV_CB_Phi.selected ops with
    op82 := .ok 113#u8
    op83 := .ok 241#u8
    op84 := ProverRwSuccessHashes.leaf
    op86 := .ok 29#usize}
theorem op82_installed (ops : ExternalFuns) : (selected ops).op82 = .ok 113#u8 := rfl
theorem op83_installed (ops : ExternalFuns) : (selected ops).op83 = .ok 241#u8 := rfl
theorem op84_installed (ops : ExternalFuns) (hash : ProverRwSuccessHashes.Hash)
    (tag : U8) (values : Slice U8) :
    (selected ops).op84 hash tag values = hash (ProverRwSuccessHashes.leafFrame tag values) := rfl
theorem op86_installed (ops : ExternalFuns) : (selected ops).op86 = .ok 29#usize := rfl
#print axioms op82_installed
#print axioms op83_installed
#print axioms op84_installed
#print axioms op86_installed
end R1Z.PV_CB_Merkle
