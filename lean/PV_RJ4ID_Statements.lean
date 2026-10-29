import PV_RJ4ID_Op79
import PV_RJ4ID_Op254
import PV_RJ4ID_Statement
import R1Z.PV_RJDec_CommonCases
import R1Z.PV_RJDec_ResultCases
set_option autoImplicit false
#check @R1Z.PV_RJ4ID_Op79.native_control
#check @R1Z.PV_RJ4ID_Op79.installation
#check @R1Z.PV_RJ4ID_PowersControl.source_unfold
#check @R1Z.PV_RJ4ID_PowersControl.dispatch_congr
#check @R1Z.PV_RJ4ID_PowersControl.loop_finite
#check @R1Z.PV_RJ4ID_PowersControl.source
#check @R1Z.PV_RJ4ID_PowersBridge.step
#check @R1Z.PV_RJ4ID_PowersBridge.finite
#check @R1Z.PV_RJ4ID_PowersBridge.complete
#check @R1Z.PV_RJ4ID_Op254.entry
#check @R1Z.PV_RJ4ID_Op254.installation
#check @R1Z.PV_RJ4ID_Statement.required_fields
#check @R1Z.PV_RJ4ID_Statement.other_index
#check @R1Z.PV_RJ4ID_Statement.consume
#check @R1Z.PV_RJDec_CommonCases.complete_pair
#check @R1Z.PV_RJDec_ResultCases.fibres_iff
#check @R1Z.PV_RJDec_V047Native.consume
#check @R1Z.PV_RJDec_V047Native.identification_iff
#print axioms R1Z.PV_RJDec_CommonCases.complete_pair
#print axioms R1Z.PV_RJDec_ResultCases.fibres_iff
#print axioms R1Z.PV_RJDec_V047Native.consume
