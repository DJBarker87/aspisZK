import NNH_ResumeOkPort
import NNH_Stage2SourceConfiguration
set_option autoImplicit false
noncomputable section
namespace NNH_AuthResumeSdk
open Aeneas Aeneas.Std AspisR1 VTop_Stages NNH_Libraries

theorem produce (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8)
 (domain : RSL.TX2_241.Dom064 V0 (LIB_Carriers.bytes pub,LIB_Carriers.bytes proof,LIB_Carriers.bytes ck))
 (success : LIBB_Tx2EnvCode.code env pub proof ck=.ok (.Ok ())) :
 ∃ p a,(DrvC_Installation.stage (NNH_RuntimeErrorValue.configuration missing env err reserve)).op18
  (LIBB_PartitionEnv.digest env) ck proof pub .S2 ()=.ok (.Ok (p,a)) ∧
 NID_ResumeFields.Domain p a ∧ a.next=10#usize := by
 obtain ⟨variant,parsed,common⟩ := NNH_AuthCodeOk.entered env pub proof ck success
 have ckSize : ck.val.length=1768 := by
  simpa only [LIB_Carriers.bytes,List.length_map,RSL.CHECKPOINT_BYTES] using domain.2.1
 obtain ⟨p,a,resumed,fields,next⟩ := NNH_CommonResumeDomain.source
  (LIBB_Tx2Reservation.reservation env) (LIBB_Tx2Reservation.reservation env)
  (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env)) (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env))
  (LIBB_PartitionEnv.digest env) pub proof ck () ckSize common
 have native := NNH_ResumeOkPort.value _ _ ck proof pub () p a resumed
 rw [LIBB_Tx2Reservation.reserved] at native
 exact ⟨p,a,native,fields,next⟩
#print axioms produce
end NNH_AuthResumeSdk
