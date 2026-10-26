import ARU_Range
import ART_ZeroArithmetic
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#print AspisR1.F3T_Numeric.total
#print AspisR1.F3T_Numeric.accountLoss
#check AspisR1.ART_ZeroArithmetic.margin
#print axioms AspisR1.ART_ZeroArithmetic.margin
#print axioms AspisR1.ART_ZeroArithmetic.positive
