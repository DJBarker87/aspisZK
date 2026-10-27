import R1Z.PDict_RemainingCommute231_18
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_UIntOps in

theorem stage19 (base : ExternalTypes)
    (ops other : @ExternalFuns (PDict_CarrierInstall.native base)) :
    PDict_UIntOps.selected base (@replace (PDict_CarrierInstall.native base) ops other) =
    @replace (PDict_CarrierInstall.native base) (PDict_UIntOps.selected base ops) other := by
  letI : ExternalTypes := PDict_CarrierInstall.native base
  let upd (d : @ExternalFuns (PDict_CarrierInstall.native base)) : @ExternalFuns (PDict_CarrierInstall.native base) :=
    { d with
    op137 := @cmp10, op138 := @cmpSame, op139 := @cmpSame,
    op140 := @compare, op161 := @makeDefault, op162 := @clone }
  have hu (d : @ExternalFuns (PDict_CarrierInstall.native base)) :
      upd (@replace (PDict_CarrierInstall.native base) d other) = @replace (PDict_CarrierInstall.native base) (upd d) other := by rfl
  change upd (@PDict_Installed.selected (PDict_CarrierInstall.native base) (@replace (PDict_CarrierInstall.native base) ops other)) =
    @replace (PDict_CarrierInstall.native base) (upd (@PDict_Installed.selected (PDict_CarrierInstall.native base) ops)) other
  exact (congrArg upd (@stage18 (PDict_CarrierInstall.native base) ops other)).trans (hu (@PDict_Installed.selected (PDict_CarrierInstall.native base) ops))

#print axioms stage19
end R1Z.PDict_RemainingCommute231
