import R1Z.PDict_RemainingCommute231_30
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_OffpathBorrow in

theorem stage31 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_OffpathBorrow.native base)) :
    PDict_OffpathBorrow.selected base (@replace (PDict_OffpathBorrow.native base) ops other) =
    @replace (PDict_OffpathBorrow.native base) (PDict_OffpathBorrow.selected base ops) other := by
  letI : ExternalTypes := PDict_OffpathBorrow.native base
  let upd (d : @ExternalFuns (PDict_OffpathBorrow.native base)) : @ExternalFuns (PDict_OffpathBorrow.native base) :=
    { d with op125 := asMut, op126 := derefMut }
  have hu (d : @ExternalFuns (PDict_OffpathBorrow.native base)) :
      upd (@replace (PDict_OffpathBorrow.native base) d other) = @replace (PDict_OffpathBorrow.native base) (upd d) other := by rfl
  change upd (PDict_ResumeDictionary.selected base (@replace (PDict_OffpathBorrow.native base) ops other)) =
    @replace (PDict_OffpathBorrow.native base) (upd (PDict_ResumeDictionary.selected base ops)) other
  exact (congrArg upd (stage30 base ops other)).trans (hu (PDict_ResumeDictionary.selected base ops))

#print axioms stage31
end R1Z.PDict_RemainingCommute231
