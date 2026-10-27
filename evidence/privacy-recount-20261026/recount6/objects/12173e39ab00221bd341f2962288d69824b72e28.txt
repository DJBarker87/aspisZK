import PV_B1_Close254
import PV_B1_Close230
import PV_B1_Close258
set_option autoImplicit false
noncomputable section
namespace PV_B1_ActualContext
open Aeneas Aeneas.Std Result ProverRwFull PV_B1_Transport PV_B1_ActualInstall
variable [ExternalTypes]
def original (ops : ExternalFuns) : ExternalFuns :=
  {ops with
    op230:=fun xs => ok (Option.map PV_B1_ActualCarrier230.fromQ
      (PV_B1_SumOriginal.original_row (sliceMap PV_B1_ActualCarrier230.toQ xs)))
    op254:=fun N x => resultMap (arrayMap PV_B1_ActualCarrierWide.fromW)
      (PV_B1_PowersOriginal.weights.powers N (PV_B1_ActualCarrierWide.toW x))
    op258:=fun v m c => PV_B1_PoleOriginal.reference.all_slots_clear
      (rows v) m (PV_B1_ActualCarrier258.toQ c)}
theorem dictionaries (ops : ExternalFuns) : selected ops=original ops := by
  have h230 : helper=(fun xs => ok (Option.map PV_B1_ActualCarrier230.fromQ
    (PV_B1_SumOriginal.original_row (sliceMap PV_B1_ActualCarrier230.toQ xs)))) := by
    funext xs; exact PV_B1_Close230.selected_callback ops xs
  have h254 : powers=(fun N x => resultMap (arrayMap PV_B1_ActualCarrierWide.fromW)
    (PV_B1_PowersOriginal.weights.powers N (PV_B1_ActualCarrierWide.toW x))) := by
    funext N x; exact PV_B1_Close254.selected_callback ops N x
  have h258 : pole=(fun v m c => PV_B1_PoleOriginal.reference.all_slots_clear
    (rows v) m (PV_B1_ActualCarrier258.toQ c)) := by
    funext v m c; exact PV_B1_Close258.selected_callback ops v m c
  unfold selected original
  rw [h230,h254,h258]
-- An arbitrary typed context can observe success, every error, or divergence.
theorem observations {O : Sort _} (observe : ExternalFuns → O) (ops : ExternalFuns) :
    observe (selected ops)=observe (original ops) := congrArg observe (dictionaries ops)
#print axioms dictionaries
#print axioms observations
end PV_B1_ActualContext
