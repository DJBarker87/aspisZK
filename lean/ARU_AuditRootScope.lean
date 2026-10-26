import ARU_RootRestriction
import Rc10_Top
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#print AspisR1.ARU_RootRestriction.WithoutBinding
#check @AspisR1.Rc10_Top.deployed
#print axioms AspisR1.Rc10_Top.deployed
