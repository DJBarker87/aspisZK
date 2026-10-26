import SCG_Interfaces
import Rc7_Top
import SCG_Charge
import SCF_Domination
set_option pp.fullNames true
set_option pp.deepTerms true
set_option format.width 120
#check @AspisR1.Rc7_Top.deployed
#print axioms AspisR1.Rc7_Top.deployed
#check @AspisR1.SCG_Charge.charged
#check @AspisR1.SCF_Domination.pointwise_of_agreement
#print AspisR1.F3T_Runtime.deployedFailure
#print AspisR1.F3T_Runtime.runtimeMass
#check @AspisR1.DrvC_SourceEntry.same_program
#check @AspisR1.DrvC_CutAcceptance.source_accepts
#print AspisR1.DrvC_PairProgram.source
#print AspisR1.F3T_Installed.source
