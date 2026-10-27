import ARV_Poison
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.maxSteps 1000000
set_option format.width 140
-- Complete binder/trust-scope audit only; zero deployed premise-removal credit.
#check @AspisR1.ARV_Poison.invalid
#print axioms AspisR1.ARV_Poison.invalid
