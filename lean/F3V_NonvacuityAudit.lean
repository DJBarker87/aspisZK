import F3V_BaselineAudit
import F3S_PrimitiveNonvacuity
import F3U_RangeMaximal
import F3U_Numeric
set_option pp.all false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
#print AspisR1.WAdm_Domain.SessionAPrepare
#print AspisR1.Port5Q1_QueryPorts.SessionAPrimitives
#print AspisR1.Port5Q1_GeometryCanonical.SessionAPrimitives
#print AspisR1.Port5Q1_Domain.SessionADomain
#print AspisR1.S2X.CheckpointVersionBinding
#print AspisR1.S2W_AuthenticatedInputs.P2Prime
#print AspisR1.CPR_DataPersistence.TwoTransactionLaw
#check @AspisR1.F3S_PrimitiveNonvacuity.accepted
#check @AspisR1.F3U_Numeric.exact
#check @AspisR1.F3U_Numeric.positive
#print AspisR1.F3U_Numeric.margin
#print AspisR1.F3U_RangeEdges.maxQueries
#check @AspisR1.F3U_RangeMaximal.exact_range
#print axioms AspisR1.F3U_Numeric.positive
#print axioms AspisR1.F3U_RangeMaximal.exact_range
