-- PCVU_ probe 2: headline stage dictionary against the Dep shape (shape only; each #check is a name test, the theorem is a restatement attempt)
import Aeneas
import PRVEq_Tx2Deployed_s1
import NNH_HostCtx
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVU_Probe
open AspisR1
#check @AspisR1.NNH_HostCtx.sdk
#check @AspisR1.DrvC_Installation.stage
#check @AspisR1.DrvC_Installation.Configuration
#check @PCVN_Tx2Deployed.Dep
#check @PCVN_Tx2Deployed.stageNNH
#check @NNH_Tx2SourceConfiguration.stage
end PCVU_Probe
