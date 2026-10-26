import R1Z.PDict_RemainingCommute231_11
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_WireError in

theorem stage12 [types : ExternalTypes] (ops other : ExternalFuns) :
    @PDict_WireError.selected types (@replace types ops other) =
    @replace types (@PDict_WireError.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with op256 := equal }
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change upd (@ProverRwDictionaryDomain.selected types (@replace (types) ops other)) =
    @replace (types) (upd (@ProverRwDictionaryDomain.selected types ops)) other
  exact (congrArg upd (@stage11 types ops other)).trans (hu (@ProverRwDictionaryDomain.selected types ops))

#print axioms stage12
end R1Z.PDict_RemainingCommute231
