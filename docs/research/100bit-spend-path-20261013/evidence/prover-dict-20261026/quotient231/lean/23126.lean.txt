import R1Z.PDict_RemainingCommute231_10
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open ProverRwDictionaryDomain in

theorem stage11 [types : ExternalTypes] (ops other : ExternalFuns) :
    @ProverRwDictionaryDomain.selected types (@replace types ops other) =
    @replace types (@ProverRwDictionaryDomain.selected types ops) other := by
  letI : ExternalTypes := types
  let upd (d : @ExternalFuns (types)) : @ExternalFuns (types) :=
    { d with op75 := fibreNew,op76 := fibreGet}
  have hu (d : @ExternalFuns (types)) :
      upd (@replace (types) d other) = @replace (types) (upd d) other := by rfl
  change upd (@ProverRwDictionaryWideQM.selected types (@replace (types) ops other)) =
    @replace (types) (upd (@ProverRwDictionaryWideQM.selected types ops)) other
  exact (congrArg upd (@stage10 types ops other)).trans (hu (@ProverRwDictionaryWideQM.selected types ops))

#print axioms stage11
end R1Z.PDict_RemainingCommute231
