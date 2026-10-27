import FIs_FinalClosure
import Rc10_Reverse
import Rc9_Transport
import FGm_AcceptedSource
import FIo_Derived
import FIn_ViewTransport
import Rc10_Top
import Rc10_Install
import Rc9_Reverse
import Rc10_Nonvacuity
import Rc10_Clean
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
#check @AspisR1.Rc10_Top.deployed
#print axioms AspisR1.Rc10_Top.deployed
#check @AspisR1.FGm_Aligned.values
#print axioms AspisR1.FGm_Aligned.values
#check @AspisR1.FGm_Join.accepted_raw_join_or_collision
#print axioms AspisR1.FGm_Join.accepted_raw_join_or_collision

#check @AspisR1.FIs_Finish.strengthen
#print axioms AspisR1.FIs_Finish.strengthen
#check @AspisR1.FIs_OnRun.strengthen
#print axioms AspisR1.FIs_OnRun.strengthen
#check @AspisR1.FIs_Headline.deployed
#print axioms AspisR1.FIs_Headline.deployed
