import NNS_SameConstant
set_option autoImplicit false
noncomputable section
namespace NNS_064Value
open Aeneas Aeneas.Std AspisR1

/-- Value-only association of the two resolved common computations. It does
not identify their traces, independent stops or chosen parent observations. -/
theorem common_result (env : RSL.Env) (pub proof ck : Slice U8) :
 (NKE_Free.eval (NNH_064CommonRecords.program env pub proof ck)).result =
 LIBB_Tx2EnvCode.common env pub proof ck := by
 have source := NKE_CommonEval.source (LIBB_Tx2Reservation.reservation env)
  (LIBB_Tx2Reservation.reservation env) (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env))
  (NLB_Parent.finish (LIBB_Tx2Reservation.reservation env))
  (LIBB_PartitionEnv.digest env) pub proof ck ()
 have same := congrArg (fun x => x.result) source
 exact same.trans (LIBB_Tx2EnvCode.source_result env pub proof ck)

#print axioms common_result
end NNS_064Value
