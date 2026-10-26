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
#check @AspisR1.SAP_PrepareOwner.installed
#print axioms AspisR1.SAP_PrepareOwner.installed
#check @AspisR1.SAP_Binding.prepare
#print axioms AspisR1.SAP_Binding.prepare
#check @AspisR1.F3Y_InstalledLaws.prepare
#print axioms AspisR1.F3Y_InstalledLaws.prepare
#check @AspisR1.SAP_SaveOnRun.saved
#print axioms AspisR1.SAP_SaveOnRun.saved
#check @AspisR1.TxS_Encoding.model
#print axioms AspisR1.TxS_Encoding.model
#check @AspisR1.SAF_AcceptedValue.value
#print axioms AspisR1.SAF_AcceptedValue.value
#check @AspisR1.S6N_Installation.facts
#print axioms AspisR1.S6N_Installation.facts
#check @AspisR1.S6N_Installation.accepted
#print axioms AspisR1.S6N_Installation.accepted
#check @AspisR1.S6N_Decoder.complete
#print axioms AspisR1.S6N_Decoder.complete
#check @AspisR1.S6N_Getters.complete
#print axioms AspisR1.S6N_Getters.complete
#check @AspisR1.Rc8_Top.deployed
#print axioms AspisR1.Rc8_Top.deployed
#check @AspisR1.FGm_Aligned.values
#print axioms AspisR1.FGm_Aligned.values
#check @AspisR1.FGm_Join.accepted_raw_join_or_collision
#print axioms AspisR1.FGm_Join.accepted_raw_join_or_collision
