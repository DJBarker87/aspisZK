import NNG_FinishDomain094
import NNG_CheckpointCall094
import NNG_FlushCall094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_CheckpointReached094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Carriers094

theorem domain (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (p : verifier.Prepared) (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
 (before after : verifier.Accumulator) (geo : verifier.QueryGeometry)
 (pending out : verifier.BatchedWeights) (ev : List RSL.Event)
 (inputDomain : LIBC_QueryLoop.Domain
  (LIB_Carriers.bytes s.proof,toT12 p,toT15 before,arr toT3 g,toT14 geo,toT13 pending,10))
 (prepared : NGC_PreparationBoundary.Fields (NFW_PreparedPort.prepared (toT12 p)))
 (returned : LIBC_QueryLoop.child.run
  (LIB_Carriers.bytes s.proof,toT12 p,toT15 before,arr toT3 g,toT14 geo,toT13 pending,10)
  env ⟨.ret (.ok (toT15 after,toT13 out)),ev⟩)
 (proofWidth : (LIB_Carriers.bytes s.proof).length=57607)
 (publicWidth : (LIB_Carriers.bytes s.publicBytes).length=1880) :
 LIBC_Checkpoint.Domain (NNG_CheckpointCall094.args p
  {after with weights:=⟨(NNG_FlushCall094.output out).val,(NNG_FlushCall094.output out).property⟩}
  s.proof s.publicBytes) := by
 apply LIBC_CheckpointDomain.from_writer _ _ proofWidth publicWidth
 have writer := NNG_FinishDomain094.writer _ env (toT15 after) (toT13 out) ev inputDomain prepared returned
 change NGC_KNE_Caller.WriterDomain (CheckpointBytes3Namespaces.toPrepared (NFW_PreparedPort.prepared (toT12 p)))
  (CheckpointBytes3Namespaces.toAccumulator (LIBC_VStateCarriers.toAcc
   (toT15 {after with weights:=⟨(NNG_FlushCall094.output out).val,(NNG_FlushCall094.output out).property⟩})))
 rw [NNG_FlushCall094.update]
 exact writer
#print axioms domain
end AspisR1.NNG_CheckpointReached094
