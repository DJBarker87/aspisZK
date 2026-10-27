import ARW_AdmittedBudget
import ARW_AdmittedQueries
import ARW_AdmittedSupport
import ARW_Carrier
import ARW_Conservativity
import ARW_Core
import ARW_DisconnectedAdmissions
import ARW_FixtureAudit
import ARW_Induced
import ARW_LocalBudget
import ARW_Nonvacuity
import ARW_Observations
import ARW_OldRoot
import ARW_QueryAgreement
import ARW_Residual
import ARW_Root
import ARW_RuntimeDomain
import ARW_WrapperNative
set_option autoImplicit false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.maxSteps 1000000
set_option format.width 140

-- Complete actual root, requested candidate and exact unresolved obligation.
#check @AspisR1.Rc10_Top.deployed
#print AspisR1.ARW_Root.Requested
#print AspisR1.ARW_Residual.Numeric
#check @AspisR1.ARW_Observations.observations
#check @AspisR1.ARW_RuntimeDomain.obstruction
#check @AspisR1.ARW_OldRoot.conservativity
#check @AspisR1.ARW_Nonvacuity.conditional
#print axioms AspisR1.Rc10_Top.deployed
#print axioms AspisR1.ARW_AdmittedBudget.issued
#print axioms AspisR1.ARW_AdmittedQueries.admitted
#print axioms AspisR1.ARW_AdmittedSupport.original
#print axioms AspisR1.ARW_Carrier.exact
#print axioms AspisR1.ARW_Conservativity.program_on_old_class
#print axioms AspisR1.ARW_Conservativity.queries_on_old_class
#print axioms AspisR1.ARW_Core.observations
#print axioms AspisR1.ARW_DisconnectedAdmissions.obstruction
#print axioms AspisR1.ARW_Induced.program
#print axioms AspisR1.ARW_Induced.issued
#print axioms AspisR1.ARW_Induced.evaluation
#print axioms AspisR1.ARW_Induced.queries
#print axioms AspisR1.ARW_Induced.output
#print axioms AspisR1.ARW_LocalBudget.issued
#print axioms AspisR1.ARW_Nonvacuity.conditional
#print axioms AspisR1.ARW_Observations.observations
#print axioms AspisR1.ARW_OldRoot.conservativity
#print axioms AspisR1.ARW_QueryAgreement.exact
#print axioms AspisR1.ARW_Residual.Numeric
#print axioms AspisR1.ARW_Residual.characterization
#print axioms AspisR1.ARW_Root.Requested
#print axioms AspisR1.ARW_RuntimeDomain.obstruction
#print axioms AspisR1.ARW_WrapperNative.first
