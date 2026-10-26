import ARU_Join
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#print AspisR1.FIp_GlobalOwners.Owners
#print AspisR1.FIp_Remaining.Holds
#check @AspisR1.ARU_Join.accepted
#print axioms AspisR1.ARU_Join.accepted
