import F3T_ModelClaims
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.maxSteps 1000000
set_option format.width 140
-- Exact cached boundary statement, not a new proof or release replay.
#check @AspisR1.F3T_ModelClaims.failure_bound
#print axioms AspisR1.F3T_ModelClaims.failure_bound
