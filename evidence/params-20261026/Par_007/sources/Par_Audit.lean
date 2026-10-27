import Par_Headline
import Par_Transcript
set_option autoImplicit false
#print axioms AspisR1.Par_Parameters.address_bound
#print axioms AspisR1.Par_Parameters.encoder_bound
#print axioms AspisR1.Par_Parameters.decoder_inverse
#print axioms AspisR1.Par_Parameters.parameter_nonvacuity
#print axioms AspisR1.Par_Parameters.input_map_add
#print axioms AspisR1.Par_Parameters.input_map_smul
#print axioms AspisR1.Par_Public.input_bytes
#print axioms AspisR1.Par_Public.accepted_public_bound
#print axioms AspisR1.Par_NativePair.accepted_pair
#print axioms AspisR1.Par_Headline.deployed
#print axioms AspisR1.Par_Transcript.accepted_initFits
set_option pp.all true in
#check @AspisR1.DrvC_NativePair.accepted_pair_driver
set_option pp.all true in
#check @AspisR1.Par_NativePair.accepted_pair
set_option pp.all true in
#check @AspisR1.DrvC_Headline.deployed_headline_installed
set_option pp.all true in
#check @AspisR1.Par_Headline.deployed
