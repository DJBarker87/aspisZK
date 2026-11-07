import NNH_CommonReservation
import NNH_AuthCodeOk
set_option autoImplicit false
noncomputable section
namespace NNH_AuthReservation
open Aeneas Aeneas.Std AspisR1 NNH_Libraries

theorem source (env : RSL.Env) (pub proof ck : Slice U8)
 (domain : RSL.TX2_241.Dom064 V0 (LIB_Carriers.bytes pub,LIB_Carriers.bytes proof,LIB_Carriers.bytes ck))
 (success : LIBB_Tx2EnvCode.code env pub proof ck=.ok (.Ok ())) : env.reservation=true := by
 obtain ⟨variant,parsed,common⟩ := NNH_AuthCodeOk.entered env pub proof ck success
 have size : ck.val.length=1768 := by
  simpa only [LIB_Carriers.bytes,NMS_R2N_RSLScalars.bytes,List.length_map,RSL.CHECKPOINT_BYTES] using domain.2.1
 have reserved := NNH_CommonReservation.source
  (LIBB_Tx2Reservation.reservation env) (LIBB_Tx2Reservation.reservation env)
  (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env)) (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env))
  (LIBB_PartitionEnv.digest env) pub proof ck () size common
 exact (LIBB_Tx2Reservation.reserved env).symm.trans reserved
#print axioms source
end NNH_AuthReservation
