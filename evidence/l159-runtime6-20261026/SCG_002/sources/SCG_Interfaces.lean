import SCF_RequiredTransport
import SCE_NativeAccepted
import DrvC_NativePair
import F3X_Join
import Rc7_Top
set_option autoImplicit false
#check AspisR1.SCF_RequiredTransport.CleanAccountTransport
#check AspisR1.DrvC_CutAcceptance.source_accepts
#check AspisR1.DrvC_SourceEntry.same_program
#check AspisR1.F3X_Join.accepted_raw_join_or_collision
#check AspisR1.SCF_Recovery.agreement
#check AspisR1.SCE_NativeAccepted.accepted
#print axioms AspisR1.Rc7_Top.deployed
