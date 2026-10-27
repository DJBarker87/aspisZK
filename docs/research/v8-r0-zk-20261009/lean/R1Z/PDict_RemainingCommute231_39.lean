import R1Z.PDict_RemainingCommute231_38
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_CodecDictionary in

theorem stage39 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_CodecDictionary.native base)) :
    PDict_CodecDictionary.selected base (@replace (PDict_CodecDictionary.native base) ops other) =
    @replace (PDict_CodecDictionary.native base) (PDict_CodecDictionary.selected base ops) other := by
  letI : ExternalTypes := PDict_CodecDictionary.native base
  let upd (d : @ExternalFuns (PDict_CodecDictionary.native base)) : @ExternalFuns (PDict_CodecDictionary.native base) :=
    { d with
    op49 := PDict_CodecSource.aspis_core.field.wide_exact.WideExact.to_limbs
    op50 := PDict_CodecSource.aspis_core.field.wide_exact.WideExact.from_le_bytes }
  have hu (d : @ExternalFuns (PDict_CodecDictionary.native base)) :
      upd (@replace (PDict_CodecDictionary.native base) d other) = @replace (PDict_CodecDictionary.native base) (upd d) other := by rfl
  change upd (PDict_PureDictionary.selected base (@replace (PDict_CodecDictionary.native base) ops other)) =
    @replace (PDict_CodecDictionary.native base) (upd (PDict_PureDictionary.selected base ops)) other
  exact (congrArg upd (stage38 base ops other)).trans (hu (PDict_PureDictionary.selected base ops))

#print axioms stage39
end R1Z.PDict_RemainingCommute231
