import R1Z.PDict_RemainingCommute231_04
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open ProverRwDictionaryTower in

theorem stage5 [types : ExternalTypes] (ops other : ExternalFuns) :
    @ProverRwDictionaryTower.selected types (@replace types ops other) =
    @replace types (@ProverRwDictionaryTower.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with
    op64 := .ok (fromQ AspisR1ProducerRelease47.field.QM31.ZERO)
    op67 := qAdd, op68 := qSub, op69 := qMul
    op45 := wEmbed, op46 := wAdd, op47 := wMul}
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change @ProverRwDictionaryBaseField.selected types (upd (@replace (types) ops other)) =
    @replace (types) (@ProverRwDictionaryBaseField.selected types (upd ops)) other
  exact (congrArg (@ProverRwDictionaryBaseField.selected types) (hu ops)).trans (@stage4 types (upd ops) other)

#print axioms stage5
end R1Z.PDict_RemainingCommute231
