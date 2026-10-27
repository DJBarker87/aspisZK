import R1Z.PDict_RemainingCommute231_32
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_CtConstructor in

theorem stage33 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_CtConstructor.native base)) :
    PDict_CtConstructor.selected base (@replace (PDict_CtConstructor.native base) ops other) =
    @replace (PDict_CtConstructor.native base) (PDict_CtConstructor.selected base ops) other := by
  letI : ExternalTypes := PDict_CtConstructor.native base
  let upd (d : @ExternalFuns (PDict_CtConstructor.native base)) : @ExternalFuns (PDict_CtConstructor.native base) :=
    { d with op218 := construct base }
  have hu (d : @ExternalFuns (PDict_CtConstructor.native base)) :
      upd (@replace (PDict_CtConstructor.native base) d other) = @replace (PDict_CtConstructor.native base) (upd d) other := by rfl
  change upd (PDict_CtUpdate.selected base (@replace (PDict_CtConstructor.native base) ops other)) =
    @replace (PDict_CtConstructor.native base) (upd (PDict_CtUpdate.selected base ops)) other
  exact (congrArg upd (stage32 base ops other)).trans (hu (PDict_CtUpdate.selected base ops))

#print axioms stage33
end R1Z.PDict_RemainingCommute231
