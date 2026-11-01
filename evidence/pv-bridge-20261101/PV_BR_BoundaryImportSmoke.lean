import PV_BR_AdmissionTransport
import NDR_CombinedAudit

/-! Boundary smoke only: this does not import the migrated event closure. -/
#check PV_BR_AdmissionTransport.validateCommon_success
#check AspisR1.NDR_CombinedAudit.sourceOnHeadline
#print axioms PV_BR_AdmissionTransport.validateCommon_roundtrip
#print axioms AspisR1.NDR_CombinedAudit.sourceOnHeadline
