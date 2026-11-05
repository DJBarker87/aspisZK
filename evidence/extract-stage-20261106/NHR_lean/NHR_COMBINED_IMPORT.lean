import NGK_COMBINED_IMPORT
import NHR_prepare.Funs
import NHR_tx1.Funs
import NHR_tx2_authenticated.Funs
import NHR_tx2_common.Funs

-- Compile-only audit: opaque callees are explicit arguments. No refinement theorem.
#check NHR_prepare.verifier.candidate.prepare
#check NHR_tx1.verifier.candidate.tx1
#check NHR_tx2_authenticated.verifier.candidate.tx2_authenticated
#check NHR_tx2_common.verifier.candidate.tx2_common
#print axioms NHR_prepare.verifier.candidate.prepare
#print axioms NHR_tx1.verifier.candidate.tx1
#print axioms NHR_tx2_authenticated.verifier.candidate.tx2_authenticated
#print axioms NHR_tx2_common.verifier.candidate.tx2_common
#print axioms AspisR1.RPx_Deployed.deployed
