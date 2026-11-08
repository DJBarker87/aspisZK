import NNY_MerkleShared
import NNU_MerkleSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNY_NNUParent
open Aeneas Aeneas.Std Result VTop_Stages
/-- NNU_REMAINING's exact parent statement, with agreement discharged. -/
theorem parent (m : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)
 (pub proof ck : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (folded : Array U8 32#usize)
 (resume : NJJ_Common.resume (LIBB_Tx2Reservation.reservation env) (LIBB_PartitionEnv.digest env)
  ck proof pub .S2 ()=.ok (.Ok (p,a)))
 (accepted : NLP_NativeMerkle.action (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
  proof p folded 1#usize ()=.ok (.Ok ())) :
 Port4B_Install.batch
  (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (NNH_CorrectConfiguration.sdk m env err r))
  proof p folded 1#usize ()=.ok (.Ok ()) := by
 change Port4B_Install.batch (LIBB_PartitionEnv.digest env) proof p folded 1#usize ()=_
 exact NNY_MerkleShared.parent (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
  (NNY_MerkleShared.tx2 env) proof p folded 1#usize (by decide)
  (NNU_MerkleSlots.same_resume env pub proof ck p a resume) accepted
#print axioms parent
end AspisR1.NNY_NNUParent
end
