import Tx2I_Witness
set_option autoImplicit false

#print axioms AspisR1.Tx2I_Install.shape_header
#print axioms AspisR1.Tx2I_Install.other_adapter_slots
#print axioms AspisR1.Tx2I_Install.other_stage_slots
#print axioms AspisR1.Tx2I_Cuts.common_source
#print axioms AspisR1.Tx2I_Cuts.tail_reached
#print axioms AspisR1.Tx2I_Cuts.common_reached
#print axioms AspisR1.Tx2I_Cuts.authenticated_reached
#print axioms AspisR1.Tx2I_Finish.accepted_finish
#print axioms AspisR1.Tx2I_Accepted.accepted_pair_claims_tx2
#print axioms AspisR1.Tx2I_Nonvacuity.extraction_satisfiable
#print axioms AspisR1.Tx2I_Nonvacuity.shape_success
#print axioms AspisR1.Tx2I_Nonvacuity.finish_success
#print axioms AspisR1.Tx2I_Witness.authenticated_success

#check AspisR1.Op3I_Accepted.accepted_pair_claims_op3
#check AspisR1.Tx2I_Accepted.accepted_pair_claims_tx2
#check AspisR1.FinT_Model.finish_value
#print AspisR1.S2W_DigestExtraction.AeneasExtraction
