import R1Z.PDict_RemainingCommute231_15
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_Primitives in

theorem stage16 [types : ExternalTypes] (ops other : ExternalFuns) :
    @PDict_Primitives.selected types (@replace types ops other) =
    @replace types (@PDict_Primitives.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with
    op0 := @sharedRef, op1 := @sliceRef,
    op207 := .ok .Left, op210 := invariant, op221 := .ok () }
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change upd (@PDict_Compare.selected types (@replace (types) ops other)) =
    @replace (types) (upd (@PDict_Compare.selected types ops)) other
  exact (congrArg upd (@stage15 types ops other)).trans (hu (@PDict_Compare.selected types ops))

#print axioms stage16
end R1Z.PDict_RemainingCommute231
