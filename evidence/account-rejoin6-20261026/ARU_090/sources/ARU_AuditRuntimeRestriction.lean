import ARU_RootRestriction
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#print AspisR1.F3T_Runtime.StoredCarrierBinding
#check @AspisR1.ARU_RootRestriction.impossible_if_native
#check @AspisR1.ART_RootObstruction.independent
#print axioms AspisR1.ARU_RootRestriction.impossible_if_native
