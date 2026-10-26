import ARU_CutsOrigin
import ARU_R1
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#check @AspisR1.ARU_CutsOrigin.selected
#check @AspisR1.ARU_R1.selected
#print axioms AspisR1.ARU_R1.selected
