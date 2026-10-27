import R1Z.PDict_RemainingCommute231_17
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_RemainingCommute231
open Aeneas Aeneas.Std Result ProverRwFull
open PDict_RemainingExt231 (replace stage0)
open PDict_Installed in

theorem stage18 [types : ExternalTypes] (ops other : ExternalFuns) :
    @PDict_Installed.selected types (@replace types ops other) =
    @replace types (@PDict_Installed.selected types ops) other := by
  exact @stage17 types ops other

#print axioms stage18
end R1Z.PDict_RemainingCommute231
