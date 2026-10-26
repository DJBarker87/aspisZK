import R1Z.PDict_RemainingCommute231_31
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_CtUpdate in

theorem stage32 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_CtUpdate.native base)) :
    PDict_CtUpdate.selected base (@replace (PDict_CtUpdate.native base) ops other) =
    @replace (PDict_CtUpdate.native base) (PDict_CtUpdate.selected base ops) other := by
  letI : ExternalTypes := PDict_CtUpdate.native base
  let upd (d : @ExternalFuns (PDict_CtUpdate.native base)) : @ExternalFuns (PDict_CtUpdate.native base) :=
    { d with op220 := updateBlocks base }
  have hu (d : @ExternalFuns (PDict_CtUpdate.native base)) :
      upd (@replace (PDict_CtUpdate.native base) d other) = @replace (PDict_CtUpdate.native base) (upd d) other := by rfl
  change upd (PDict_OffpathBorrow.selected base (@replace (PDict_CtUpdate.native base) ops other)) =
    @replace (PDict_CtUpdate.native base) (upd (PDict_OffpathBorrow.selected base ops)) other
  exact (congrArg upd (stage31 base ops other)).trans (hu (PDict_OffpathBorrow.selected base ops))

#print axioms stage32
end R1Z.PDict_RemainingCommute231
