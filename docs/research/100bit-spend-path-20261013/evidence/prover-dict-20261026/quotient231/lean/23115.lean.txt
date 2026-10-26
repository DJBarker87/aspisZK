import R1Z.PDict_RemainingCommute231_01
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open ProverRwOuterMapErr in

theorem stage2 [types : ExternalTypes] (ops other : ExternalFuns) :
    @ProverRwOuterMapErr.selected types (@replace types ops other) =
    @replace types (@ProverRwOuterMapErr.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with op12 := @map_err}
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change @ProverRwOuterGuardLeaves.selected types (upd (@replace (types) ops other)) =
    @replace (types) (@ProverRwOuterGuardLeaves.selected types (upd ops)) other
  exact (congrArg (@ProverRwOuterGuardLeaves.selected types) (hu ops)).trans (@stage1 types (upd ops) other)

#print axioms stage2
end R1Z.PDict_RemainingCommute231
