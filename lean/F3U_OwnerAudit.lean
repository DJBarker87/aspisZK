import F3U_SamePair
import F3U_SourceCost
import F3S_PrimitiveNonvacuity
set_option pp.all false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 120
#print AspisR1.F3T_Leaves.Holds
#print AspisR1.WAdm_Domain.SessionAPrepare
#print AspisR1.Port5Q1_QueryPorts.SessionAPrimitives
#print AspisR1.Port5Q1_GeometryCanonical.SessionAPrimitives
#print AspisR1.Port5Q1_Domain.SessionADomain
#print AspisR1.S2X.CheckpointVersionBinding
#print AspisR1.S2W_AuthenticatedInputs.P2Prime
#check @AspisR1.F3S_PrimitiveNonvacuity.accepted
#check @AspisR1.F3U_SourceCost.cost_or_collision
#print axioms AspisR1.F3U_SourceCost.cost_or_collision
