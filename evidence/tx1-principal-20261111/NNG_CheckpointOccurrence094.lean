import NNG_InvokeGraph094
import NNG_CheckpointCall094
import NNG_Tree094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_CheckpointOccurrence094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Carriers094

theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (p : verifier.Prepared) (a : verifier.Accumulator)
 (domain : LIBC_Checkpoint.Domain (NNG_CheckpointCall094.args p a s.proof s.publicBytes)) :
 LIB_Instances.VL.checkpoint.run
  (toT12 p,toT15 a,LIB_Carriers.bytes s.proof,LIB_Carriers.bytes s.publicBytes) env
  (NNG_Observed136.observation (fun v : alloc.vec.Vec U8=>LIB_Carriers.bytes v.deref) (NNG_Events094.events env)
   (NNG_Tree094.NNG_call_6 (NNG_InstalledCalls094.calls env).c6 s.digest p a s.proof s.publicBytes s.hash)) := by
 unfold NNG_Tree094.NNG_call_6
 rw [NNG_InvokeGraph094.observation,NNG_Events094.checkpoint_call]
 exact NNG_CheckpointCall094.graph env p a s.proof s.publicBytes domain
#print axioms source
end AspisR1.NNG_CheckpointOccurrence094
