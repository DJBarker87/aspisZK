import RPx_Margin
import RPx_Top
import RPx_Nonvacuity
import RPx_AccountCharge
import RPx_Obstruction
import RPx_PreAccept
import RPx_RejectMass
import RPx_FailedQuery
set_option pp.all false
set_option pp.deepTerms true
set_option pp.explicit false
set_option pp.fullNames true
set_option pp.universes false
set_option format.width 120
#check @AspisR1.Rc7_Top.deployed
#check @AspisR1.RPx_Top.deployed
#check @AspisR1.RPx_Nonvacuity.composed
#check @AspisR1.RPx_Transport.transport
#check @AspisR1.RPx_Transport.charged
#check @AspisR1.RPx_NativeTransport.first
#check @AspisR1.RPx_NativeTransport.second
#check @AspisR1.RPx_AccountBudget.budget
#check @AspisR1.RPx_AccountCharge.charged
#print axioms AspisR1.RPx_Top.deployed
#print axioms AspisR1.RPx_Nonvacuity.composed
