import R1Z.PDict_RemainingCommute231_03
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open ProverRwDictionaryBaseField in

theorem stage4 [types : ExternalTypes] (ops other : ExternalFuns) :
    @ProverRwDictionaryBaseField.selected types (@replace types ops other) =
    @replace types (@ProverRwDictionaryBaseField.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with
    op57 := AspisR1Qm31ArithmeticProbe.field.M31.mul
    op58 := AspisR1Qm31ArithmeticProbe.field.M31.double
    op73 := AspisR1Qm31ArithmeticProbe.field.M31.add
    op74 := AspisR1Qm31ArithmeticProbe.field.M31.sub}
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change @ProverRwDictionaryDigest.selected types (upd (@replace (types) ops other)) =
    @replace (types) (@ProverRwDictionaryDigest.selected types (upd ops)) other
  exact (congrArg (@ProverRwDictionaryDigest.selected types) (hu ops)).trans (@stage3 types (upd ops) other)

#print axioms stage4
end R1Z.PDict_RemainingCommute231
