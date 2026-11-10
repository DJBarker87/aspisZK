import Aeneas
import NNH_Tx2SourceConfiguration
import NNH_CorrectConfiguration
import PRVEq_AdapterStage1_o1
import PRVEq_AdapterStage2_o1
import PRVEq_CallerPrepTx1_o1
open Aeneas Aeneas.Std
set_option autoImplicit false
noncomputable section
#check @NNH_Tx2SourceConfiguration.sdk
#check @DrvC_Installation.sdk
#check @DrvC_Installation.currentInstalled
#check @DrvC_Installation.current
#check @NNH_CorrectConfiguration.configuration
#check @NNH_CorrectConfiguration.sdk
#check @NNH_Tx2Configuration.configuration
#check @AdapterRw.r1_pool_adapter.owned.stage1_owned
#check @AspisR1CurrentCaller.verifier.candidate.prepare
#check @AspisR1CurrentCaller.verifier.candidate.tx1
#print NNH_CorrectConfiguration.sdk
#print NNH_CorrectConfiguration.configuration
