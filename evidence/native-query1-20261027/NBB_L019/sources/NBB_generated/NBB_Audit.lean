import NBB_Arithmetic
import NBB_Cohort
import NBB_Finish
import NBB_Nonvacuity
import NBB_Phase
import NBB_Push
import NBB_QueryTrace
import NBB_QueryWitness
import NBB_Row
import NBB_RowTrace
import NBB_RowWitness
import NBB_Sweep

set_option autoImplicit false

#print axioms NBB_Arithmetic.add
#print axioms NBB_Arithmetic.fold
#print axioms NBB_Finish.source
#print axioms NBB_Finish.unique
#print axioms NBB_Nonvacuity.row
#print axioms NBB_Nonvacuity.finish
#print axioms NBB_Phase.next
#print axioms NBB_Phase.scalar
#print axioms NBB_Phase.unique
#print axioms NBB_Push.source
#print axioms NBB_Push.sweep
#print axioms NBB_QueryTrace.unroll
#print axioms NBB_QueryTrace.native_result
#print axioms NBB_QueryWitness.construct
#print axioms NBB_QueryWitness.direct
#print axioms NBB_Row.source
#print axioms NBB_Row.unique
#print axioms NBB_RowTrace.frame_unique
#print axioms NBB_RowTrace.steps_result
#print axioms NBB_RowTrace.source_result
#print axioms NBB_RowTrace.native_result
#print axioms NBB_RowWitness.steps
#print axioms NBB_RowWitness.construct
#print axioms NBB_Sweep.initial
#print axioms NBB_Sweep.update
#print axioms NBB_Sweep.final
#check NBB_RowTrace.native_result
#check NBB_RowWitness.construct
#check NBB_QueryWitness.direct
#check NBB_Finish.source
