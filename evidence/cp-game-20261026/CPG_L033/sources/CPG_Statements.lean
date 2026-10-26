import CPG_Top
import CPG_CPS
import CPG_Nonvacuity
import CPP_Endpoint
import CPR_PhysicalOrder
set_option autoImplicit false
set_option pp.universes false
set_option pp.fullNames true
#check @AspisR1.T2R_Top.deployed
#check @AspisR1.CPG_Top.deployed
#check @AspisR1.CPG_Pair.accepted
#check @AspisR1.CPG_CPS.correlated
#print AspisR1.CPG_Game.DeployedPairExecution
#print AspisR1.CPG_Projection.Observations
#print AspisR1.CPG_Projection.entry
#print AspisR1.CPG_Projection.loaded
#print AspisR1.CPG_Projection.ordinary
#print AspisR1.CPG_Projection.tentative
#print AspisR1.CPG_RuntimeTrace.Step
#print AspisR1.CPG_RuntimeTrace.Executes
#print AspisR1.CPR_DataPersistence.TwoTransactionLaw
#print AspisR1.CPR_PhysicalResult.Outcome
#print AspisR1.CPP_Acceptance.Facts
#print AspisR1.CPP_CallerSource.Outcome
#check @AspisR1.CPP_Endpoint.deployed
#print axioms AspisR1.CPG_Projection.dead
#print axioms AspisR1.CPG_Projection.live
#print axioms AspisR1.CPG_Game.next
#print axioms AspisR1.CPG_Accepted.writer_positive
#print axioms AspisR1.CPG_Accepted.writer_ordinary
#print axioms AspisR1.CPG_Accepted.reader_positive
#print axioms AspisR1.CPG_History.tentative_view
#print axioms AspisR1.CPG_History.physical_result
#print axioms AspisR1.CPG_History.entry2_view
#print axioms AspisR1.CPG_History.on_cuts
#print axioms AspisR1.CPG_Pair.accepted
#print axioms AspisR1.CPG_Nonvacuity.game
#print axioms AspisR1.CPG_Nonvacuity.RuntimePersistence
#print axioms AspisR1.CPG_Nonvacuity.nonempty
#print axioms AspisR1.CPG_Account.bound
#print axioms AspisR1.CPG_Account.zero
#print axioms AspisR1.CPG_Top.deployed
#print axioms AspisR1.CPG_CPS.correlated

#print axioms AspisR1.CPG_RuntimeTrace.step_effect
#print axioms AspisR1.CPG_RuntimeTrace.result
#print axioms AspisR1.CPG_RuntimeTrace.step_exists
#print axioms AspisR1.CPG_RuntimeTrace.executes
