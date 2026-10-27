import PV_B1_AuditAllRows
set_option autoImplicit false
noncomputable section
namespace PV_B1_ClosureReplay
open ProverRwFull PV_B1_ActualInstall
-- A focused import-cone replay: every original-signature row and its source
-- bridge is loaded from the validated private frozen cone.
theorem closing_dictionary [ExternalTypes] (ops : ExternalFuns) :
    selected ops=PV_B1_ActualContext.original ops :=
  PV_B1_ActualContext.dictionaries ops
#print axioms closing_dictionary
#check PV_B1_254.source
#check PV_B1_230.source
#check PV_B1_258.source
#check PV_B1_Close254.nonfailure
#check PV_B1_Close230.nonvacuity
#check PV_B1_PoleWitnesses.nonempty
#check PV_B1_PoleWitnesses.failure_nonvacuity
#check PV_B1_Nonvacuity.joint_success
end PV_B1_ClosureReplay
