import R1Z.PDict_RemainingCommute231_08
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open ProverRwDictionaryMerkle in

theorem stage9 [types : ExternalTypes] (ops other : ExternalFuns) :
    @ProverRwDictionaryMerkle.selected types (@replace types ops other) =
    @replace types (@ProverRwDictionaryMerkle.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with
    op119 := AspisR1ProverLeaf.state_only_private_merkle.private_leaf_hash}
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change upd (@ProverRwDictionaryDerived.selected types (@replace (types) ops other)) =
    @replace (types) (upd (@ProverRwDictionaryDerived.selected types ops)) other
  exact (congrArg upd (@stage8 types ops other)).trans (hu (@ProverRwDictionaryDerived.selected types ops))

#print axioms stage9
end R1Z.PDict_RemainingCommute231
