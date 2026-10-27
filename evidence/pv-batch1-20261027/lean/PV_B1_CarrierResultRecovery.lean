import PV_B1_CarrierContainers
import PV_B1_ResultFaithful
set_option autoImplicit false
noncomputable section
namespace PV_B1_CarrierResultRecovery
open Aeneas Aeneas.Std Result PV_B1_Transport
theorem wide (N : Usize) (r : Result (Array PV_B1_CarrierWide.W N)) :
    resultMap (arrayMap PV_B1_CarrierWide.toW)
      (resultMap (arrayMap PV_B1_CarrierWide.fromW) r)=r := by
  apply result_roundtrip
  intro v
  exact array_roundtrip _ _ PV_B1_CarrierWide.to_from v

theorem sum (r : Result (Option PV_B1_Carrier230.Q)) :
    resultMap (Option.map PV_B1_Carrier230.toQ)
      (resultMap (Option.map PV_B1_Carrier230.fromQ) r)=r := by
  apply result_roundtrip
  intro v
  cases v with
  | none => rfl
  | some q => simp only [Option.map_some,PV_B1_Carrier230.to_from]
#print axioms wide
#print axioms sum
end PV_B1_CarrierResultRecovery
