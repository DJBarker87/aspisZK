import Rc8_Transport
import FGm_AcceptedSource
import FIo_Derived
import FIn_ViewTransport
import Rc8_Top
import Rc8_Install
import Rc8_Reverse
import Rc8_Nonvacuity
import Rc8_Clean
import Rc8_Event
import FGm_Aligned
import FGm_Join
import FIn_QuarterAlias
set_option pp.all false
set_option pp.deepTerms true
set_option pp.explicit false
set_option pp.fullNames true
set_option pp.universes false
set_option format.width 120
#print AspisR1.FGm_Owners.Owners
#print AspisR1.FGm_Owners.Holds
#print AspisR1.FGl_PreparedAt.Owners
#print AspisR1.FGl_FinishLeaves.Holds
#print AspisR1.FGl_FinishLeaves.PairingRemaining
#check @AspisR1.FGm_Aligned.values
#check @AspisR1.FGm_Join.accepted_raw_join_or_collision
#print axioms AspisR1.FGm_Aligned.values
