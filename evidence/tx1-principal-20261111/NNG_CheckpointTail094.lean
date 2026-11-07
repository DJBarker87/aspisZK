import NNG_Terminal094
import NNG_CheckpointOccurrence094
import NNG_MapObservation094
import NNG_SourceStep136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_CheckpointTail094
open Aeneas Aeneas.Std Result NMT_tx1 NMT_CallTree NNG_Observed136 NNG_Carriers094
/-- One source-ordered checkpoint occurrence followed by the silent mark.
Its original Domain is consumed at the exact updated accumulator argument. -/
theorem source (env : RSL.Env) (s : NNG_Context094.Parent Unit)
 (p : verifier.Prepared) (a : verifier.Accumulator) (weights : alloc.vec.Vec aspis_core.field.QM31)
 (observer : s.observer=none)
 (domain : LIBC_Checkpoint.Domain (NNG_CheckpointCall094.args p {a with weights:=weights} s.proof s.publicBytes)) :
 RSL.RE.bind (RSL.RE.lift (LIB_Instances.VL.checkpoint.run
  (toT12 p,toT15 {a with weights:=weights},LIB_Carriers.bytes s.proof,LIB_Carriers.bytes s.publicBytes)))
  (fun bytes=>RSL.RE.pure bytes) env
  (observation NNG_Producer094.port (NNG_Events094.events env)
   (NNG_Tree094.f_bytes (NNG_InstalledCalls094.calls env) s p a weights)) := by
 let code := NNG_Tree094.NNG_call_6 (NNG_InstalledCalls094.calls env).c6
  s.digest p {a with weights:=weights} s.proof s.publicBytes s.hash
 let tail : alloc.vec.Vec U8 → Code NNG_Context094.Output := fun bytes=>
  NNG_Tree094.f_markCheckpointWrite (NNG_InstalledCalls094.calls env) s bytes
 have head := NNG_CheckpointOccurrence094.source env s p {a with weights:=weights} domain
 have lifted := NNG_MapObservation094.mapped (fun v : alloc.vec.Vec U8=>LIB_Carriers.bytes v.deref)
  (Except.ok : RSL.Bytes → Except LIB_VCarriers.VErr RSL.Bytes)
  (NNG_Events094.events env) code env _ head
 change RSL.Spec.bind (RSL.RE.lift (LIB_Instances.VL.checkpoint.run
  (toT12 p,toT15 {a with weights:=weights},LIB_Carriers.bytes s.proof,LIB_Carriers.bytes s.publicBytes))) _ env
  (observation NNG_Producer094.port (NNG_Events094.events env) (NMT_CallTree.bind code tail))
 apply NNG_SourceStep136.bind_sound code tail
  (fun v : alloc.vec.Vec U8=>(Except.ok (LIB_Carriers.bytes v.deref) : Except LIB_VCarriers.VErr RSL.Bytes))
  NNG_Producer094.port (NNG_Events094.events env) env _ _ lifted
 intro bytes returned
 exact NNG_Terminal094.source env s bytes observer
#print axioms source
end AspisR1.NNG_CheckpointTail094
