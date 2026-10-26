import Rc6_Top
import FGl_Headline
import FGl_Transport
import FGl_Nonvacuity
import Rc4_Top
import Rc5_Top
import Rc5_ResultForget
import Rc5_RuntimeFixture
import Rc5_Nonrejecting
import Rc5_DictionaryNonvacuity
import Rc4_Nonvacuity
import Rc4_ResultForget
import CPH_Top
import SAF_Deployed
import SAQ_CompleteTop
import TxS_Top
set_option pp.all false
set_option pp.deepTerms true
set_option pp.explicit false
set_option pp.fullNames true
set_option pp.universes false
set_option format.width 120
#check @AspisR1.Rc5_Source.source
#check @AspisR1.Rc5_Close.from_saf
#check @AspisR1.Rc5_ResultForget.forget
#check @AspisR1.SAF_ForgetFinish.forget
#check @AspisR1.Rc4_Top.deployed
#check @AspisR1.Rc5_Top.deployed
#check @AspisR1.CPH_Top.deployed
#check @AspisR1.SAF_Deployed.deployed
#print AspisR1.Rc4_Statement.Conclusion
#print AspisR1.Rc5_Result.Outcome

#check @AspisR1.F3Y_Headline.deployed
#check @AspisR1.F3Y_Nonvacuity.composed
#print axioms AspisR1.F3Y_Headline.deployed
#print axioms AspisR1.F3Y_Nonvacuity.composed

#check @AspisR1.Rc6_Top.deployed
#check @AspisR1.FGl_Headline.deployed
#check @AspisR1.FGl_Nonvacuity.composed
