import ARQ_BankCut
import ARU_ByteMatch
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#check @AspisR1.ARQ_BankCut.checkpoint
#check @AspisR1.ARU_ByteMatch.digest_matches
#print axioms AspisR1.ARU_ByteMatch.digest_matches
