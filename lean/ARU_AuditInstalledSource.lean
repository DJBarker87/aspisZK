import ARU_FullSourceAlternative
import ARQ_SourceAlternative
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#check @AspisR1.ARQ_SourceAlternative.accepted
#check @AspisR1.ARU_FullSourceAlternative.accepted
#print axioms AspisR1.ARU_FullSourceAlternative.accepted
