import PV_B3P_Closure226
import PV_B3P_FreePadding132
import PV_B3P_MaskLoopBounds132

-- Complete V243 packet; V228 supporting laws remain below whole-row closure.
#print axioms PV_B3P_Closure226.complete_result
#print axioms PV_B3P_Closure226.value
#print axioms PV_B3P_Closure226.nonvacuity
#print axioms PV_B3P_WholeBuffer226.value
#print axioms PV_B3P_NativePlan226.complete_result
#print axioms PV_B3P_NativeIdentities226.frontier_groups
#print axioms PV_B3P_ResultSpine226.padding
#print axioms PV_B3P_FreeTotal132.total
#print axioms PV_B3P_FreePadding132.value
#print axioms PV_B3P_MaskModel132.member_iff
#print axioms PV_B3P_MaskPath132.used_iff
#print axioms PV_B3P_MaskStep132.write_retained
#print axioms PV_B3P_MaskStep132.inner_done
#print axioms PV_B3P_MaskStep132.outer_done
#print axioms PV_B3P_MaskLoopBounds132.row_next
#print axioms PV_B3P_MaskLoopBounds132.column_next
#print axioms PV_B3P_MaskLoopBounds132.count_next
