import CPS_SourceTop
import CPS_Ordinary
import CPS_LawBoundary
import CPS_BankTransaction
import CPS_FailedParent
import CPR_PhysicalTop
set_option autoImplicit false

-- Before/after and exact runtime-admission interfaces; no new axiom or law.
#check @AspisR1.T2R_Top.deployed
#check @AspisR1.CPR_PhysicalTop.deployed
#check @AspisR1.CPS_SourceTop.correlated
#check @AspisR1.S2W_D189Consolidation.RuntimeEntrypointAdmission
#check @AspisR1.CPR_DataPersistence.TwoTransactionLaw
#print axioms AspisR1.T2R_Top.deployed
#print axioms AspisR1.CPS_SourceTop.correlated
#print axioms AspisR1.CPS_BankSource.step_effect
#print axioms AspisR1.CPS_BankRecorder.result
#print axioms AspisR1.CPS_BankRecorder.events
#print axioms AspisR1.CPS_BankTransaction.evaluation
#print axioms AspisR1.CPS_BankTransaction.source_result
#print axioms AspisR1.CPS_BankTransaction.query_frame
#print axioms AspisR1.CPS_BankTransaction.failed
#print axioms AspisR1.CPS_BoundaryLoad.writer_positive
#print axioms AspisR1.CPS_PhysicalKey.pairing
#print axioms AspisR1.CPS_Ordinary.owner
#print axioms AspisR1.CPS_Ordinary.of_flags
#print axioms AspisR1.CPS_ParentStatus.success_iff
#print axioms AspisR1.CPS_FailedParent.accepted_copy
#print axioms AspisR1.CPS_ParentBoundary.accepted_pair
#print axioms AspisR1.CPS_LawBoundary.populated
#print axioms AspisR1.CPS_LawBoundary.law_only_eliminates
