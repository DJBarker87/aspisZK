import NJC_ConcreteUnwrap
import NJC_ValidateCalls
set_option autoImplicit false
noncomputable section
namespace NJC_RawCalls
open Aeneas Aeneas.Std Result AspisR1 NIL_Carriers

/-- Same literal resume call sites with concrete frozen raw-reader source and
complete fresh validator installed. All other OPEN operations stay named. -/
def resume (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (v : Fresh.V) (hash : H) :=
 NID_ResumeEmission.verifier.resume
 CheckpointBytes4Ops.ne CheckpointBytes4Ops.eq NIL_FreshOps.mapError NIL_FreshOps.any
 (fun x=>ok x) (ok (unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))
 (NIL_FreshOps.filled reserved) NIL_FreshOps.semantic NIL_FreshOps.weights
 NJC_ValidateEmission.verifier.validate_checkpoint_queries
 NIL_FreshOps.readK NIL_FreshOps.readE NJC_ConcreteUnwrap.raw
 (fun v=>CheckpointBytes4Ops.checkpointSize (variant v))
 (fun v=>CheckpointBytes4Ops.finalLen (variant v))
 (fun v=>CheckpointBytes4Ops.tag (variant v)) (NIL_FreshOps.digest d)
 bytes proof public1 v hash


theorem reference (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (v : Fresh.V) (hash : H) :
 resume reserved d bytes proof public1 v hash=
 NJC_ValidateCalls.resume reserved d bytes proof public1 v hash := by
 have same : NJC_ConcreteUnwrap.raw=NIL_FreshOps.raw :=
  funext (fun n=>funext (NJC_ConcreteUnwrap.clause n))
 unfold resume NJC_ValidateCalls.resume
 rw [same]

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (hash : H) :
 NIL_StatePort.reply (resume reserved d bytes proof public1 .S2 hash)=
 AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) d bytes proof public1 .S2 hash := by
 rw [reference]
 exact NJC_ValidateCalls.source reserved d bytes proof public1 hash

#print axioms reference
#print axioms source
end NJC_RawCalls
