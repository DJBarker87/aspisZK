import ARU_Range
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#check @AspisR1.ARU_Mass.conditional
#check @AspisR1.ARU_Numeric.conditional
#check @AspisR1.ARU_Range.conditional
#print axioms AspisR1.ARU_Numeric.conditional
