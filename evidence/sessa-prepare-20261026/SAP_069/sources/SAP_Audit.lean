import SAP_ClosedTop
import SAP_ActualTop
import SAP_Top
import SAP_CloseConsumer
set_option pp.all false
set_option pp.deepTerms true
set_option pp.explicit false
set_option pp.fullNames true
set_option pp.universes false
set_option format.width 120
#check @AspisR1.T2R_Top.deployed
#check @AspisR1.SAP_Top.deployed
#check @AspisR1.SAP_ActualTop.deployed
#check @AspisR1.SAP_ClosedTop.deployed
#print AspisR1.SAP_ClosedFull.Outcome
#print AspisR1.SAP_ClosedCaller.Outcome
#print AspisR1.SAP_ClosedCont.Outcome
#print AspisR1.SAP_ClosedOutcome.Outcome
#print AspisR1.SAP_FinishSaved.Outcome
#print AspisR1.T2R_FullResult.Outcome
#print AspisR1.T2R_CallerSource.Outcome
#print AspisR1.T2R_ContSource.Outcome
#print AspisR1.T2R_Ten.Outcome
#print AspisR1.T2R_Finish.Outcome
#print AspisR1.SAP_Install.configuration
#print AspisR1.WAdm_Domain.SessionAPrepare
#print AspisR1.Port5Q1_QueryPorts.SessionAPrepare
#print AspisR1.Port5Q2_Prepared.SessionAPrepare
#print AspisR1.Port5Q2_Prepared.PreparedFields
#print AspisR1.T2R_Acceptance.Facts
#print axioms AspisR1.SAP_ClosedTop.deployed
#print axioms AspisR1.SAP_ClosedPair.accepted
#print axioms AspisR1.SAP_CloseConsumer.close
#print axioms AspisR1.SAP_SaveOnRun.saved
#print axioms AspisR1.SAP_SourceConsumer.from_cut
#print axioms AspisR1.SAP_ActualPair.accepted
#print axioms AspisR1.SAP_Attach.from_cut
#print axioms AspisR1.SAP_PrepareOwner.installed
