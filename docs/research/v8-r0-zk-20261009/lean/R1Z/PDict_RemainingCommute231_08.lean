import R1Z.PDict_RemainingCommute231_07
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open ProverRwDictionaryDerived in

theorem stage8 [types : ExternalTypes] (ops other : ExternalFuns) :
    @ProverRwDictionaryDerived.selected types (@replace types ops other) =
    @replace types (@ProverRwDictionaryDerived.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with
    op53 := AspisR1ProverMaterial14.aspis_core.field.M31.Insts.CoreCloneClone.clone
    op54 := mEq
    op62 := ProverRwDictionaryDerivedSource.aspis_core.field.QM31.Insts.CoreCloneClone.clone
    op63 := qEq}
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change upd (@ProverRwDictionaryLayout.selected types (@replace (types) ops other)) =
    @replace (types) (upd (@ProverRwDictionaryLayout.selected types ops)) other
  exact (congrArg upd (@stage7 types ops other)).trans (hu (@ProverRwDictionaryLayout.selected types ops))

#print axioms stage8
end R1Z.PDict_RemainingCommute231
