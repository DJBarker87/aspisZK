import F3U_BytePreparation
import F3U_PublicOracleValue
import F3U_CollisionJoin
set_option pp.all false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 120
-- These all-world source observations do NOT construct the full native-pair
-- interface or establish the canonical Join. Their different result types and
-- the original native/digest boundary are printed together for the handoff.
#check @AspisR1.F3U_AllWorldMachine.accepted
#check @AspisR1.F3U_BytePreparation.accepted
#check @AspisR1.F3U_PublicOracleValue.initial
#check @AspisR1.F3U_PublicOracleValue.public_value
#print AspisR1.F3U_Rehash.dictionary
#print AspisR1.S2W_ExtractionBoundary.AeneasExtraction
#print AspisR1.S2W_ExtractionBoundary.RuntimeSyscall
#print AspisR1.F3U_CollisionJoin.Join
#print axioms AspisR1.F3U_BytePreparation.accepted
