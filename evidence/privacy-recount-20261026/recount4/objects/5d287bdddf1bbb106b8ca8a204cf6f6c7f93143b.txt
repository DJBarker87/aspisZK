import R1Z.ProverRwDictionaryEmbedding
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryConstants
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryEmbedding.selected ops with
    op82 := .ok 113#u8
    op83 := .ok 241#u8
    op86 := .ok 29#usize
    op111 := .ok 18224775710398755665#u64}

theorem entry82 (ops : ExternalFuns) : (selected ops).op82 = .ok 113#u8 := rfl
#print axioms entry82

theorem entry83 (ops : ExternalFuns) : (selected ops).op83 = .ok 241#u8 := rfl
#print axioms entry83

theorem entry86 (ops : ExternalFuns) : (selected ops).op86 = .ok 29#usize := rfl
#print axioms entry86

theorem entry111 (ops : ExternalFuns) : (selected ops).op111 = .ok 18224775710398755665#u64 := rfl
#print axioms entry111

end R1Z.ProverRwDictionaryConstants
