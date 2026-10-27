import ARU_Charges
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#print AspisR1.ART_AdversaryWork.work
#print AspisR1.ART_AdversaryWork.Bound
#check @AspisR1.ARU_Charges.charged
#print axioms AspisR1.ARU_Charges.charged
