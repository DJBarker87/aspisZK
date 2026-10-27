import JGs_Regular
import JGs_InactiveCoefficients
import FJv_Top
set_option autoImplicit false
namespace AspisR1.JGs_Obstruction70
open Aeneas Aeneas.Std Result
/-- Exact next producing gate, with no successful Pair as a premise. -/
def PairGoal : Prop := FIo_Install.pair (.Ok ()) JGo_TX2_WeightData.value JGo_TX2_FinishPrefix.alphas
  (JFw_Frames.window 8007 2048) JFo_Prepared.value.kappa=ok (.Ok JGo_TX2_Horner1_6.after)
#print PairGoal
#print axioms AspisR1.JGs_K1.source
#print axioms AspisR1.JGs_K3.source
#print axioms AspisR1.JGs_K4.source
#print axioms AspisR1.JGs_Regular.source
#print axioms AspisR1.JGs_Inactive.coefficients
#print axioms AspisR1.FJv_Top.deployed
#check @AspisR1.FJv_Top.deployed
end AspisR1.JGs_Obstruction70
