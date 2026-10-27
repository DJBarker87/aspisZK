import R1Z.PDict_RemainingCommute231_14
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_Compare in

theorem stage15 [types : ExternalTypes] (ops other : ExternalFuns) :
    @PDict_Compare.selected types (@replace types ops other) =
    @replace types (@PDict_Compare.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with
    op135 := @terminal, op136 := @terminalLess _,
    op187 := @equalTrue, op195 := @lessTrue }
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change upd (@PDict_Numeric.selected types (@replace (types) ops other)) =
    @replace (types) (upd (@PDict_Numeric.selected types ops)) other
  exact (congrArg upd (@stage14 types ops other)).trans (hu (@PDict_Numeric.selected types ops))

#print axioms stage15
end R1Z.PDict_RemainingCommute231
