import ARV_FinalAudit
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.maxSteps 1000000
set_option format.width 140

-- Complete final types; actual Rc10 has not been changed.
#check @AspisR1.Rc10_Top.deployed
#print AspisR1.ARV_Root.Proposed
#check @AspisR1.ARV_OneTuple.obstruction
#check @AspisR1.ARV_NativeCostGap.obstruction
#check @AspisR1.ARV_FilterTop.proposed
#check @AspisR1.ARV_Nonvacuity.conditional
#print axioms AspisR1.Rc10_Top.deployed
#print axioms AspisR1.ARV_OneTuple.obstruction
#print axioms AspisR1.ARV_NativeCostGap.obstruction
#print axioms AspisR1.ARV_FilterTop.proposed
#print axioms AspisR1.ARV_Nonvacuity.conditional
