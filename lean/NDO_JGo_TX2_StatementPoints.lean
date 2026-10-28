import NDO_JGo_TX2_WeightPoints
import NDO_JGo_TX2_WeightPointTail
import NDO_JGo_TX2_StatementTools
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_StatementPoints
open Aeneas Aeneas.Std Result FIn_WeightsExtract JGo_TX2_WeightData

theorem source : state_only_prefix.r0.statement_points alpha=ok points :=
  JGo_TX2_StatementTools.source alpha successor10 JGo_TX2_WeightPointTail.first absorption
    (alpha.val[7]) (JGo_TX2_WeightPointTail.first.val[6])
    JGo_TX2_WeightPointTail.minus7 JGo_TX2_WeightPointTail.minus6
    JGo_TX2_WeightPoints.loop (by rfl) JGo_TX2_WeightPointTail.sub7
    JGo_TX2_WeightPointTail.update7 (by rfl) JGo_TX2_WeightPointTail.sub6
    JGo_TX2_WeightPointTail.update6
#print axioms source
end AspisR1.JGo_TX2_StatementPoints
end
