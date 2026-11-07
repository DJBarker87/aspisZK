import NNG_StateCalls094
import LIBC_Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_CheckpointCall094
open Aeneas Aeneas.Std Result NMT_tx1 NNG_Carriers094

def args (p : verifier.Prepared) (a : verifier.Accumulator) (proof publicBytes : Slice U8) :
 LIBC_Checkpoint.Args := (toT12 p,toT15 a,LIB_Carriers.bytes proof,LIB_Carriers.bytes publicBytes)
def call (env : RSL.Env) (p : verifier.Prepared) (a : verifier.Accumulator)
 (proof publicBytes : Slice U8) : Result (alloc.vec.Vec U8) :=
 let out := LIBC_Checkpoint.output (args p a proof publicBytes) env
 ok ⟨out.val,out.property⟩
def events (env : RSL.Env) (p : verifier.Prepared) (a : verifier.Accumulator)
 (proof publicBytes : Slice U8) := LIBC_Checkpoint.events (args p a proof publicBytes) env

/-- Revision4 supplies the SAME public-byte extent; the writer and original
proof extent remain explicit support premises until their reached producers
are discharged in the parent fold. -/
theorem domain (input : RSL.TX1_094.Args LIB_Instances.VL) (obs : RSL.Observer)
 (hd : RSL.TX1_094.Domain LIB_Instances.VL input obs input.public_)
 (p : verifier.Prepared) (a : verifier.Accumulator) (proof publicBytes : Slice U8)
 (sameProof : LIB_Carriers.bytes proof=input.proof)
 (samePublic : LIB_Carriers.bytes publicBytes=input.public_bytes)
 (width : input.proof.length=57607)
 (writer : NGC_KNE_Caller.WriterDomain (LIBC_Checkpoint.prepared (args p a proof publicBytes))
   (LIBC_Checkpoint.accumulator (args p a proof publicBytes))) :
 LIBC_Checkpoint.Domain (args p a proof publicBytes) := by
 apply LIBC_CheckpointDomain.from_writer _ writer
 · change (LIB_Carriers.bytes proof).length=57607
   rw [sameProof]
   exact width
 · change (LIB_Carriers.bytes publicBytes).length=1880
   rw [samePublic]
   exact hd.2.2
#print axioms domain

theorem graph (env : RSL.Env) (p : verifier.Prepared) (a : verifier.Accumulator)
 (proof publicBytes : Slice U8) (hd : LIBC_Checkpoint.Domain (args p a proof publicBytes)) :
 LIBC_Checkpoint.child.run (args p a proof publicBytes) env
  (LIB_Carriers.resultObs (fun v : alloc.vec.Vec U8 => LIB_Carriers.bytes v.deref)
   (events env p a proof publicBytes) (call env p a proof publicBytes)) := by
 refine ⟨hd,hd,Or.inl ?_⟩
 rfl
#print axioms graph

theorem source (env : RSL.Env) (p : verifier.Prepared) (a : verifier.Accumulator)
 (proof publicBytes : Slice U8) :
 CheckpointBytes5Effect.run (LIBC_Checkpoint.digest env) ()
  (CheckpointBytes5Writer.writer (LIBC_Checkpoint.prepared (args p a proof publicBytes))
   (LIBC_Checkpoint.accumulator (args p a proof publicBytes))
   (LIBC_Bytes.raw (LIB_Carriers.bytes proof)) (LIBC_Bytes.raw (LIB_Carriers.bytes publicBytes))) [] =
 ok (LIBC_Checkpoint.output (args p a proof publicBytes) env,
  LIBC_Checkpoint.calls (args p a proof publicBytes) env) :=
 LIBC_Checkpoint.run_model (args p a proof publicBytes) env
#print axioms source
end AspisR1.NNG_CheckpointCall094
