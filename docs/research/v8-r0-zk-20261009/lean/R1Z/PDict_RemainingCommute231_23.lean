import R1Z.PDict_RemainingCommute231_22
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_Options in

theorem stage23 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_IOCarriers.native base)) :
    PDict_Options.selected base (@replace (PDict_IOCarriers.native base) ops other) =
    @replace (PDict_IOCarriers.native base) (PDict_Options.selected base ops) other := by
  letI : ExternalTypes := PDict_IOCarriers.native base
  let upd (d : @ExternalFuns (PDict_IOCarriers.native base)) : @ExternalFuns (PDict_IOCarriers.native base) :=
    { d with
    op19 := make,op20 := write,op21 := createNew,op24 := mode }
  have hu (d : @ExternalFuns (PDict_IOCarriers.native base)) :
      upd (@replace (PDict_IOCarriers.native base) d other) = @replace (PDict_IOCarriers.native base) (upd d) other := by rfl
  change upd (PDict_IOCarriers.selected base (@replace (PDict_IOCarriers.native base) ops other)) =
    @replace (PDict_IOCarriers.native base) (upd (PDict_IOCarriers.selected base ops)) other
  exact (congrArg upd (stage22 base ops other)).trans (hu (PDict_IOCarriers.selected base ops))

#print axioms stage23
end R1Z.PDict_RemainingCommute231
