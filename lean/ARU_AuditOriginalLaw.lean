import ARU_IndexedOriginalLaw
import ARU_OriginalAverage
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#check @AspisR1.ARU_IndexedOriginalLaw.original_law
#check @AspisR1.ARU_OriginalAverage.averaged
#print axioms AspisR1.ARU_IndexedOriginalLaw.original_law
#print axioms AspisR1.ARU_OriginalAverage.averaged
