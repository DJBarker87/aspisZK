import R1Z.PDict_RemainingCommute231_02
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open ProverRwDictionaryDigest in

theorem stage3 [types : ExternalTypes] (ops other : ExternalFuns) :
    @ProverRwDictionaryDigest.selected types (@replace types ops other) =
    @replace types (@ProverRwDictionaryDigest.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with
    op38 := AspisR1ProverLeaf.digest.LegacyHashFn.Insts.CoreCloneClone.clone
    op39 := AspisR1ProverLeaf.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32.digest}
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change @ProverRwOuterMapErr.selected types (upd (@replace (types) ops other)) =
    @replace (types) (@ProverRwOuterMapErr.selected types (upd ops)) other
  exact (congrArg (@ProverRwOuterMapErr.selected types) (hu ops)).trans (@stage2 types (upd ops) other)

#print axioms stage3
end R1Z.PDict_RemainingCommute231
