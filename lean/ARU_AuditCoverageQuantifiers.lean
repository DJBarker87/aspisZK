import ARU_CoverageQuantifiers
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#print AspisR1.ARU_CoverageQuantifiers.OriginalCoverage
#print AspisR1.ARU_AllWorld.Supported
#check @AspisR1.ARU_CoverageQuantifiers.exact_iff
#print axioms AspisR1.ARU_CoverageQuantifiers.exact_iff
