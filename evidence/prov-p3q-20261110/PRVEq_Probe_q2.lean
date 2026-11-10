import Aeneas
import PRVEq_Tx2Deployed_n1
import NJZ_Readers
import NIL_FreshOps
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section
namespace PCVQ_Probe2
open VTop_Stages VTop_Stages.PRVFresh_VTop_l1 AspisR1
#print VTop_Checkpoint.digest
#print core.result.Result.Insts.CoreOpsTry.branch
#print core.result.Result.Insts.CoreOpsFromResidual.from_residual
example {α β γ : Type} (m : Result α) (f : α → Result β) (g : β → Result γ) :
   (m >>= f) >>= g = m >>= fun a => f a >>= g := by simp
#check @bind_assoc
#check @PRVC.ite_bind
#print VTop_Stages.PRVFresh_VTop_l1.verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
#print VTop_Stages.PRVFresh_VTop_l1.verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool.call_mut
#check @AspisR1Stage2.verifier.resumeWithOps
#print AspisR1Stage2.aspis_core.digest.Digest32
#print VTop_Stages.PRVFresh_VTop_l1.aspis_core.field.QM31.Insts.CoreMarkerCopy
#print AspisR1.CheckpointBytes4Ops.headerLoop
#check @VTop_Stages.PRVFresh_VTop_l1.verifier.Reader.k
#print AspisR1.NIL_FreshOps.digest
end PCVQ_Probe2
