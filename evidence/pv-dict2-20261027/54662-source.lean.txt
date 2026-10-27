import R1Z.PDict_RemainingCommute231_21
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open ProverRwFull
open PDict_IOCarriers in

theorem stage22 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_IOCarriers.native base)) :
    PDict_IOCarriers.selected base (@replace (PDict_IOCarriers.native base) ops other) =
    @replace (PDict_IOCarriers.native base) (PDict_IOCarriers.selected base ops) other := by
  exact stage21 (PDict_IOCarriers.native base) ops other

#print axioms stage22
end R1Z.PDict_RemainingCommute231
