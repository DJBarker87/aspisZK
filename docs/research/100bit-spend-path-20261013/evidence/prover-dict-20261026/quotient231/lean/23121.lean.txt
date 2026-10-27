import R1Z.PDict_RemainingCommute231_06
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open ProverRwDictionaryLayout in

theorem stage7 [types : ExternalTypes] (ops other : ExternalFuns) :
    @ProverRwDictionaryLayout.selected types (@replace types ops other) =
    @replace types (@ProverRwDictionaryLayout.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with
    op237 := .ok ProverRwDictionaryLayoutSource.compact.SLOT_NODES
    op241 := ProverRwDictionaryLayoutSource.compact.LOGICAL_SEMANTIC
    op242 := ProverRwDictionaryLayoutSource.compact.PROOF_BYTES
    op243 := ProverRwDictionaryLayoutSource.compact.OFF_NODES
    op244 := ProverRwDictionaryLayoutSource.compact.OFF_OPENINGS
    op245 := .ok ProverRwDictionaryLayoutSource.compact.MAGIC}
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change upd (@ProverRwDictionaryScalar.selected types (@replace (types) ops other)) =
    @replace (types) (upd (@ProverRwDictionaryScalar.selected types ops)) other
  exact (congrArg upd (@stage6 types ops other)).trans (hu (@ProverRwDictionaryScalar.selected types ops))

#print axioms stage7
end R1Z.PDict_RemainingCommute231
