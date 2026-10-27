import R1Z.PDict_RemainingCommute231_19
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open Aeneas Aeneas.Std ProverRwFull
open PDict_MoreCarriers in

theorem stage20 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_MoreCarriers.native base)) :
    PDict_MoreCarriers.selected base (@replace (PDict_MoreCarriers.native base) ops other) =
    @replace (PDict_MoreCarriers.native base) (PDict_MoreCarriers.selected base ops) other := by
  exact stage19 (PDict_MoreCarriers.native base) ops other

#print axioms stage20
end R1Z.PDict_RemainingCommute231
