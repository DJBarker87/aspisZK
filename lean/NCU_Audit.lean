import NCT_DriverDomain
import NCH_Audit
import NCG_Audit
set_option autoImplicit false
#print AspisR1CurrentCaller.Ops
#print AspisR1.Port3_NativeQueryBody.Ops
#print AspisR1PublicPreparation.FinishModel.Boundaries
#check AspisR1CurrentCaller.PrepareReachability.prepare_success
#check NBO_WriterEntry.same_writer
#print NBO_ProducerDomains.NBA_NBC
#check AspisR1.NBR_PrepareTotal.source
#check AspisR1.NCA_ReturnedScanInputs.source
#check NBZ_Folds.circle_total

#print axioms NBO_WriterEntry.same_writer
#print axioms AspisR1.NBR_PrepareTotal.source
#print axioms AspisR1.NCA_ReturnedScanInputs.source
#print axioms NBZ_Folds.circle_total
