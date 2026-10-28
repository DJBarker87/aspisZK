import NDO_JGo_TX2_WeightConstruct
import NDO_JGo_TX2_StatementPoints
import NDO_JGo_TX2_WeightsTools
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_NewWeights
open Aeneas Aeneas.Std Result FIn_WeightsExtract JGo_TX2_WeightData
attribute [local irreducible] weights_new

theorem native : weights_new .S2 alpha z=ok (.Ok value) :=
  JGo_TX2_WeightsTools.source alpha z points factors00 factors15 factors25
    (alpha.val[8]) (alpha.val[9]) JGo_TX2_StatementPoints.source
    (by rfl) (by rfl) (by rfl)
    JGo_TX2_WeightConstruct.firstLoop JGo_TX2_WeightConstruct.secondLoop
#print axioms native

theorem source : FIn_WeightsInstall.newWeights JFo_Prepared.value.variant
    JFo_Prepared.value.semantic_alpha JFo_Prepared.value.z=ok (.Ok value) := by
  apply FIn_WeightsInstall.same_call
  change weights_new .S2 (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toQ JFo_Prepared.value.semantic_alpha)
    (FIn_WeightsInstall.mapArray FIn_WeightsInstall.toPoint JFo_Prepared.value.z)=ok (.Ok value)
  rw [alpha_pin,z_pin]
  exact native
#print axioms source
end AspisR1.JGo_TX2_NewWeights
end
