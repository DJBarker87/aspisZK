import NIM_NHJ_COMBINED_IMPORT
import NHT_AdapterInstall
import NHL_Tx1Model
set_option autoImplicit false
-- This checks the actual interfaces. It introduces no boundary axiom/theorem.
#check AspisR1.NHL_Tx1Model.source
#check NHT_Tx2AuthModel.source
#check NHT_AdapterInstall.slot
#check NHT_AdapterInstall.cohort_slot
#check NHT_AdapterInstall.digest_error_frame
#print axioms AspisR1.NHL_Tx1Model.source
#print axioms NHT_Tx2AuthModel.source
#print axioms NHT_AdapterInstall.cohort_slot
#print axioms AspisR1.RPx_Deployed.deployed
