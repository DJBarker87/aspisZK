import R1Z.PDict_RemainingCommute231_20
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open Aeneas Aeneas.Std ProverRwFull
open PDict_ErrorCarrier in

theorem stage21 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_ErrorCarrier.native base)) :
    PDict_ErrorCarrier.selected base (@replace (PDict_ErrorCarrier.native base) ops other) =
    @replace (PDict_ErrorCarrier.native base) (PDict_ErrorCarrier.selected base ops) other := by
  exact stage20 (PDict_ErrorCarrier.native base) ops other

#print axioms stage21
end R1Z.PDict_RemainingCommute231
