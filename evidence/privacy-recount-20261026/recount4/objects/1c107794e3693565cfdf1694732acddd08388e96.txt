import R1Z.ProverRwOuterMapErr
import AspisR1ProverLeaf.Funs

/-! Selected source operations. The digest remains the same arbitrary callback;
no purity, ROM law, output equality assumption or native effect claim is added. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryDigest
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  ProverRwOuterMapErr.selected {ops with
    op38 := AspisR1ProverLeaf.digest.LegacyHashFn.Insts.CoreCloneClone.clone
    op39 := AspisR1ProverLeaf.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest}

theorem clone_installed (ops : ExternalFuns) (hash : aspis_core.digest.LegacyHashFn) :
    @aspis_core.digest.LegacyHashFn.Insts.CoreCloneClone.clone _ (selected ops) hash =
      .ok hash := rfl

theorem digest_installed (ops : ExternalFuns) (hash : aspis_core.digest.LegacyHashFn)
    (parts : Slice (Slice U8)) :
    @aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest _
      (selected ops) hash parts = hash parts := rfl

#print axioms clone_installed
#print axioms digest_installed
end R1Z.ProverRwDictionaryDigest
