import NNU_MerkleSlots
import NKV_OkTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_MerkleNative
open Aeneas Aeneas.Std Result VTop_Stages

theorem batch (env : RSL.Env) (proof : Slice U8) (p : verifier.Prepared)
 (folded : Array U8 32#usize)
 (accepted : NLP_NativeMerkle.action (LIBB_PartitionEnv.H env) (LIBB_PartitionEnv.digest env)
  proof p folded 1#usize ()=.ok (.Ok ())) :
 Port3_NativeBatchBody.verifier.candidate.batch_merkle
  (NKV_ConcreteChildren.ops (LIBB_PartitionEnv.H env))
  (NKV_ConcreteChildren.digest (LIBB_PartitionEnv.H env)) proof p folded 1#usize ()=.ok (.Ok ()) := by
 have source := NHT_ResultSuccess.source _ () accepted
 exact (NKV_OkTransport.batch (LIBB_PartitionEnv.H env) proof p folded 1#usize (by decide)).mpr source
#print axioms batch
end AspisR1.NNU_MerkleNative
end
