import Rc8_Top
import Rc8_Nonvacuity
import SCJ_Composition
import SCJ_Nonvacuity
set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 160
#check @AspisR1.Rc8_Top.deployed
#check @AspisR1.Rc8_Nonvacuity.composed
#check @AspisR1.F3T_Runtime.StoredCarrierBinding
#print AspisR1.F3T_Runtime.StoredCarrierBinding
#print axioms AspisR1.Rc8_Top.deployed
#print axioms AspisR1.SCJ_Composition.account_of_branch
#print axioms AspisR1.SCJ_Checkpoint.same_saved
#print axioms AspisR1.SCJ_Checkpoint.entry_saved
#print axioms AspisR1.SCJ_Projection.event_implies_refuted
