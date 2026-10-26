import ARU_Charge
import ART_FullCharge
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#check @AspisR1.ARU_Charge.cached_preparation
#check @AspisR1.ART_FullCharge.charged
#print axioms AspisR1.ARU_Charge.cached_preparation
