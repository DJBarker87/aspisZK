import NNU_Inactive
import NNH_CommonResumeDomain
set_option autoImplicit false
namespace AspisR1.NNU_CommonResume
open Aeneas Aeneas.Std Result VTop_Stages

theorem occurrence (env : RSL.Env) (pub proof ck : Slice U8)
 (size : ck.val.length=1768)
 (success : LIBB_Tx2EnvCode.common env pub proof ck=.ok (.Ok ()))
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (resume : NJJ_Common.resume (LIBB_Tx2Reservation.reservation env) (LIBB_PartitionEnv.digest env)
  ck proof pub .S2 ()=.ok (.Ok (p,a))) :
 NID_ResumeFields.Domain p a ∧ a.next=10#usize := by
 obtain ⟨p0,a0,resume0,fields,next⟩ := NNH_CommonResumeDomain.source
  (LIBB_Tx2Reservation.reservation env) (LIBB_Tx2Reservation.reservation env)
  (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env))
  (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env)) (LIBB_PartitionEnv.digest env)
  pub proof ck () size success
 have same : (p0,a0)=(p,a) := core.result.Result.Ok.inj (Result.ok.inj (resume0.symm.trans resume))
 cases same
 exact ⟨fields,next⟩
#print axioms occurrence
end AspisR1.NNU_CommonResume
