import R1Z.PoleMassR1
import R1Z.PV_Inv_ModelPack
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Inv_BadContainment
open R0P R0Z.HonestValidity PV_Inv_Pack PV_Inv_ModelRow PV_Inv_PackOperands
variable {K : Type} [Field K] [DecidableEq K]

theorem producer_zero_is_pole (t : Trace K) (lam chi : K) (b : Fin 1024)
    (active : CopyActiveRow b) (weights : Fin 2 → K) (s : Slots K)
    (run : PV_Inv_PackList.run PV_Inv_Pack.empty (entries t lam b CopyLink.producer weights)=some s)
    (zero : 0 ∈ operands chi s) : ¬ NoPole t lam chi := by
  intro hp
  exact PV_Inv_ModelPack.producer t lam chi b active weights hp s run 0 zero rfl

theorem consumer_zero_is_pole (t : Trace K) (lam chi : K) (b : Fin 1024)
    (active : CopyActiveRow b) (weights : Fin 2 → K) (s : Slots K)
    (run : PV_Inv_PackList.run PV_Inv_Pack.empty (entries t lam b CopyLink.consumer weights)=some s)
    (zero : 0 ∈ operands chi s) : ¬ NoPole t lam chi := by
  intro hp
  exact PV_Inv_ModelPack.consumer t lam chi b active weights hp s run 0 zero rfl

#print axioms producer_zero_is_pole
#print axioms consumer_zero_is_pole
end R1Z.PV_Inv_BadContainment
