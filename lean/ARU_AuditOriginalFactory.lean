import ARU_OriginalFactory
import ARU_ObstructionResolved
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#check @AspisR1.ARU_OriginalFactory.original
#check @AspisR1.ARU_ObstructionResolved.installed
#print axioms AspisR1.ARU_ObstructionResolved.installed
