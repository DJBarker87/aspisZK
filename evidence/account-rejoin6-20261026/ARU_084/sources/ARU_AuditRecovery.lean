import ARU_OriginalRecovery
import ARQ_PerCoin
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#check @AspisR1.ARQ_PerCoin.extract
#check @AspisR1.ARU_OriginalRecovery.extract
#print axioms AspisR1.ARU_OriginalRecovery.extract
