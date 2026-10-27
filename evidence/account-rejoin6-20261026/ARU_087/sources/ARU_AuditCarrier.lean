import ARU_Carrier
import ART_Carrier
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#check @AspisR1.ARU_Carrier.exact
#check @AspisR1.ART_Carrier.projection
#check @AspisR1.ART_Carrier.checkpoint
#print axioms AspisR1.ARU_Carrier.exact
