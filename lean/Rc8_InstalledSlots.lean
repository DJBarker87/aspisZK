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
#print AspisR1.FIo_Install.finishOps
#print AspisR1.FIo_Install.select
#print AspisR1.FIo_Install.configuration
#print AspisR1.FIn_WeightsInstall.install
#print AspisR1.FIn_Install.finishOps
#check @AspisR1.FIo_Install.slots
#check @AspisR1.Rc8_Install.arithmetic
#check @AspisR1.Rc8_Install.complete_pair
#print AspisR1.S6N_Installation.Facts
#check @AspisR1.S6N_Installation.accepted
