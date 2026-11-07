import NNH_064ResumeRecord
import NNH_064Parser
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064ResumeError
open Aeneas Aeneas.Std VTop_Stages NJU_CommonObserved NLT_NativeInvocation
open NNH_064ResumeRecord

def reply (env : RSL.Env) (r : NP6_StdModel.Reservation) (pub proof ck : Slice U8) :=
 NLB_ResumePacket.action NLP_ResumeInstall.native r (LIBB_PartitionEnv.digest env) ck proof pub ()

theorem decoded (env : RSL.Env) (r : NP6_StdModel.Reservation) (pub proof ck : Slice U8) :
 (NKE_CommonCodec.resume ck proof pub).decode (actual (record env r pub proof ck))=
 some (reply env r pub proof ck) := by
 simp only [NKE_CommonCodec.resume,actual,record,NLT_NativeWindows.window,reply]
 simp only [and_self,ite_true]

/-- Entered common arm whose actual resume call returns Err. The error is a
branch condition of this call, never an own-input clause or successful child.
No C04/query call or post-stop suffix is constructed. -/
theorem common (env : RSL.Env) (r : NP6_StdModel.Reservation) (pub proof ck : Slice U8)
 (error : verifier.Error) (returned : reply env r pub proof ck=.ok (.Err error)) :
 NLT_CompleteRoot.Native (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
 pub proof ck () (.resolved (.ok (.Err error)) [record env r pub proof ck]) := by
 change Invocation _ _ _ (NKE_Free.Program.call (NKE_CommonCodec.resume ck proof pub) _ _) _ _
 refine Invocation.call_ok _ _ _ (record env r pub proof ck) ?_ (.Err error) ?_ _ [] ?_
 · rfl
 · rw [decoded,returned]
 · apply Invocation.prim_ok
   apply Invocation.prim_ok
   exact Invocation.ret _

#print axioms decoded
#print axioms common
end AspisR1.NNH_064ResumeError
