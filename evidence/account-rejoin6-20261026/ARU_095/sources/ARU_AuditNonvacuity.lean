import ARU_Nonvacuity
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 140
-- Statement/trust inventory only; zero premise-removal credit.
#check @AspisR1.ARU_Nonvacuity.conditional
#check AspisR1.JFx_NativeBytes.publicBytes
#check AspisR1.JFx_NativeBytes.proofBytes
#print axioms AspisR1.ARU_Nonvacuity.conditional
