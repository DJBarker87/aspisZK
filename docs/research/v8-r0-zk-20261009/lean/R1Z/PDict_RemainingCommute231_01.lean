import R1Z.PDict_RemainingExt231
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open ProverRwOuterGuardLeaves in

theorem stage1 [types : ExternalTypes] (ops other : ExternalFuns) :
    @ProverRwOuterGuardLeaves.selected types (@replace types ops other) =
    @replace types (@ProverRwOuterGuardLeaves.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with op112 := mask,op113 := factor}
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change @ProverRwOuterTag.selected types (upd (@replace (types) ops other)) =
    @replace (types) (@ProverRwOuterTag.selected types (upd ops)) other
  exact (congrArg (@ProverRwOuterTag.selected types) (hu ops)).trans (@stage0 types (upd ops) other)

#print axioms stage1
end R1Z.PDict_RemainingCommute231
