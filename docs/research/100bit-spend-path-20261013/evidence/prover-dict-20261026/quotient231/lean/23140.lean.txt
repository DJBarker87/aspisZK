import R1Z.PDict_RemainingCommute231_23
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_FinalDictionary in

theorem stage24 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_FinalDictionary.native base)) :
    PDict_FinalDictionary.selected base (@replace (PDict_FinalDictionary.native base) ops other) =
    @replace (PDict_FinalDictionary.native base) (PDict_FinalDictionary.selected base ops) other := by
  exact stage23 base ops other

#print axioms stage24
end R1Z.PDict_RemainingCommute231
