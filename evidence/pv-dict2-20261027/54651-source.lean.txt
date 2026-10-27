import R1Z.PDict_RemainingCommute231_13
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_Numeric in

theorem stage14 [types : ExternalTypes] (ops other : ExternalFuns) :
    @PDict_Numeric.selected types (@replace types ops other) =
    @replace types (@PDict_Numeric.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with
    op141 := @op141,
    op142 := @op142,
    op143 := @op143,
    op144 := @op144,
    op145 := @op145,
    op146 := @op146,
    op147 := @op147,
    op148 := @op148,
    op149 := @op149,
    op150 := @op150,
    op151 := @op151,
    op152 := @op152,
    op153 := @op153,
    op154 := @op154,
    op155 := @op155,
    op156 := @op156,
    op157 := @op157,
    op158 := @op158,
    op159 := @op159,
    op160 := @op160 }
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change upd (@PDict_Typenum.selected types (@replace (types) ops other)) =
    @replace (types) (upd (@PDict_Typenum.selected types ops)) other
  exact (congrArg upd (@stage13 types ops other)).trans (hu (@PDict_Typenum.selected types ops))

#print axioms stage14
end R1Z.PDict_RemainingCommute231
