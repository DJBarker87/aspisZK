import AspisFailureBoundModel
/-! X5 checks a and b (tool, nothing proved): statements and axioms of the two model theorems. -/
set_option pp.fullNames true
set_option format.width 100000
#check @AspisFailureBoundModel.failure_bound40P_model
#check @AspisFailureBoundModel.failure_le_per_query_model
#print axioms AspisFailureBoundModel.failure_bound40P_model
#print axioms AspisFailureBoundModel.failure_le_per_query_model
set_option pp.all true in
#check @AspisFailureBoundModel.failure_bound40P_model
set_option pp.all true in
#check @AspisFailureBoundModel.failure_le_per_query_model
