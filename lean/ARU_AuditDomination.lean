import ARU_Domination
import ARU_RuntimeMass
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#check @AspisR1.ARU_Domination.pointwise
#check @AspisR1.ARU_RuntimeMass.pointwise
#print axioms AspisR1.ARU_Domination.pointwise
