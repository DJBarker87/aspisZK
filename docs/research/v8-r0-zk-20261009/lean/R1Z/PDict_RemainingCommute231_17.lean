import R1Z.PDict_RemainingCommute231_16
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_Ordering in

theorem stage17 [types : ExternalTypes] (ops other : ExternalFuns) :
    @PDict_Ordering.selected types (@replace types ops other) =
    @replace types (@PDict_Ordering.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with op185 := @lessEq, op186 := @less }
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change upd (@PDict_Primitives.selected types (@replace (types) ops other)) =
    @replace (types) (upd (@PDict_Primitives.selected types ops)) other
  exact (congrArg upd (@stage16 types ops other)).trans (hu (@PDict_Primitives.selected types ops))

#print axioms stage17
end R1Z.PDict_RemainingCommute231
