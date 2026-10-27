import RPt_BEl_Top
import RPt_BEl_LocalCut
import RPt_BEl_PhysicalCut
import RPt_BEl_GateBounds
import RPt_BEl_Nonvacuity
set_option pp.all false
set_option pp.deepTerms true
set_option pp.fullNames true
set_option pp.explicit false
set_option pp.universes false
set_option format.width 140
#check @AspisR1.Rc10_Top.deployed
#check @AspisR1.BEl_Top.deployed
#check @AspisR1.BEl_NativeBatchCut.observation
#check @AspisR1.BEl_PhysicalCut.transfer
#check @AspisR1.BEl_OriginalReference.selected
#check @AspisR1.BEl_AccountComposition.conditional
#print axioms AspisR1.Rc10_Top.deployed
#print axioms AspisR1.BEl_Top.deployed
#print axioms AspisR1.BEl_Top.original_account
#print axioms AspisR1.BEl_NativeBatchCut.observation
#print axioms AspisR1.BEl_PhysicalCut.transfer
#print axioms AspisR1.BEl_LocalCut.current
#print axioms AspisR1.BEl_LocalCut.stage
#print axioms AspisR1.BEl_Nonvacuity.rejected
