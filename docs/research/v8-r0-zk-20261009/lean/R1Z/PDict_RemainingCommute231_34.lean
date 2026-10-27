import R1Z.PDict_RemainingCommute231_33
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_VolatileCell in

theorem stage34 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_VolatileCell.native base)) :
    PDict_VolatileCell.selected base (@replace (PDict_VolatileCell.native base) ops other) =
    @replace (PDict_VolatileCell.native base) (PDict_VolatileCell.selected base ops) other := by
  letI : ExternalTypes := PDict_VolatileCell.native base
  let upd (d : @ExternalFuns (PDict_VolatileCell.native base)) : @ExternalFuns (PDict_VolatileCell.native base) :=
    { d with op124 := overwrite }
  have hu (d : @ExternalFuns (PDict_VolatileCell.native base)) :
      upd (@replace (PDict_VolatileCell.native base) d other) = @replace (PDict_VolatileCell.native base) (upd d) other := by rfl
  change upd (PDict_CtConstructor.selected base (@replace (PDict_VolatileCell.native base) ops other)) =
    @replace (PDict_VolatileCell.native base) (upd (PDict_CtConstructor.selected base ops)) other
  exact (congrArg upd (stage33 base ops other)).trans (hu (PDict_CtConstructor.selected base ops))

#print axioms stage34
end R1Z.PDict_RemainingCommute231
