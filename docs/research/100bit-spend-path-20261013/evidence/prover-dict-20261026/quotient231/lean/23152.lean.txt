import R1Z.PDict_RemainingCommute231_35
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_FileCarrier in

theorem stage36 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_FileCarrier.native base)) :
    PDict_FileCarrier.selected base (@replace (PDict_FileCarrier.native base) ops other) =
    @replace (PDict_FileCarrier.native base) (PDict_FileCarrier.selected base ops) other := by
  exact stage35 ({ base with op0 := PDict_FileCarrier.File }) ops other

#print axioms stage36
end R1Z.PDict_RemainingCommute231
