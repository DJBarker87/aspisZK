import R1Z.PDict_RemainingCommute231_34
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_FileFlush in

theorem stage35 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_FileFlush.native base)) :
    PDict_FileFlush.selected base (@replace (PDict_FileFlush.native base) ops other) =
    @replace (PDict_FileFlush.native base) (PDict_FileFlush.selected base ops) other := by
  letI : ExternalTypes := PDict_FileFlush.native base
  let upd (d : @ExternalFuns (PDict_FileFlush.native base)) : @ExternalFuns (PDict_FileFlush.native base) :=
    { d with op17 := flush }
  have hu (d : @ExternalFuns (PDict_FileFlush.native base)) :
      upd (@replace (PDict_FileFlush.native base) d other) = @replace (PDict_FileFlush.native base) (upd d) other := by rfl
  change upd (PDict_VolatileCell.selected base (@replace (PDict_FileFlush.native base) ops other)) =
    @replace (PDict_FileFlush.native base) (upd (PDict_VolatileCell.selected base ops)) other
  exact (congrArg upd (stage34 base ops other)).trans (hu (PDict_VolatileCell.selected base ops))

#print axioms stage35
end R1Z.PDict_RemainingCommute231
