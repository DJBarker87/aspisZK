import ARQ_Transport
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.maxSteps 1000000
set_option format.width 140
-- Exact cached boundary statement, not a new proof or release replay.
#check @AspisR1.ARQ_Join.accepted_recovery_or_account_collision
#print axioms AspisR1.ARQ_Join.accepted_recovery_or_account_collision
