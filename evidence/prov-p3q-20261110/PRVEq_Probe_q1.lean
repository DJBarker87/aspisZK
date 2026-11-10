import Aeneas
import PRVEq_Tx2Deployed_n1
import NJZ_Readers
import NIL_FreshOps
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVQ_Probe
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1
#check @VTop_Stages.PRVFresh_VTop_l1.verifier.Reader.raw
#check @VTop_Stages.PRVFresh_VTop_l1.verifier.Reader.k
#check @VTop_Stages.PRVFresh_VTop_l1.verifier.Reader.e
#check @VTop_Stages.PRVFresh_VTop_l1.verifier.validate_checkpoint_queries
#print VTop_Stages.PRVFresh_VTop_l1.verifier.Reader.raw
#print VTop_Stages.PRVFresh_VTop_l1.verifier.validate_checkpoint_queries
#print VTop_Stages.PRVFresh_VTop_l1.verifier.validate_checkpoint_queries_loop
#check @AspisR1.Port3_CheckpointInstall.error
#print AspisR1.Port3_CheckpointInstall.error
#print AspisR1.CheckpointBytes4Ops.validate
#print AspisR1.CheckpointBytes4Ops.headerAny
#print AspisR1.CheckpointBytes4Ops.eq
#print AspisR1.CheckpointBytes4Ops.checkpointSize
#print AspisR1.CheckpointBytes4Ops.tag
#check @AspisR1.CheckpointBytes4Ops.readSemanticAlpha
#check @AspisR1.Port4A_NativeReader.resume
#print AspisR1.CheckpointBytes3Allocation.filled
#check @AspisR1.Port4A_ReaderNormalize.source
end PCVQ_Probe
