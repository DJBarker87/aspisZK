import R1Z.PDict_RemainingCommute231_29
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_ResumeDictionary in

theorem stage30 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_ResumeDictionary.native base)) :
    PDict_ResumeDictionary.selected base (@replace (PDict_ResumeDictionary.native base) ops other) =
    @replace (PDict_ResumeDictionary.native base) (PDict_ResumeDictionary.selected base ops) other := by
  exact stage29 base ops other

#print axioms stage30
end R1Z.PDict_RemainingCommute231
