import SAP_FrozenSdk
import SAP_FrozenSource
set_option pp.all false
set_option pp.deepTerms true
set_option pp.explicit false
set_option pp.fullNames true
set_option pp.universes false
set_option format.width 120
#check @AspisR1.F3T_SourcePair.accepted_pair
#check @AspisR1.SAP_FrozenSource.accepted_pair
#check @AspisR1.SAP_FrozenSdk.accepted
#print AspisR1.F3T_Leaves.Holds
#print AspisR1.F3S_FinishWitness.Primitives
#print AspisR1.F3S_AcceptanceValues.Values
#print axioms AspisR1.SAP_FrozenSource.accepted_pair
#print axioms AspisR1.SAP_FrozenSdk.accepted
