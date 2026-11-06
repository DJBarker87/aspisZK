import NJC_ValidatePort
import NIY_ResumePort
set_option autoImplicit false
noncomputable section
namespace NJC_ValidateCalls
open Aeneas Aeneas.Std Result AspisR1 NIL_Carriers NIL_ResultTransport

/-- Invert only the proved nominal error port; no result clause is assumed. -/
theorem clause (queries : Array U32 22#usize) :
 NJC_ValidateEmission.verifier.validate_checkpoint_queries queries=NIL_FreshOps.validate queries := by
 have roundtrip : ∀ x : core.result.Result Unit Fresh.Err,
   unInner id (NIL_Carriers.inner id x)=x :=
  fun x=>inner_roundtrip id id (fun _=>rfl) x
 unfold NIL_FreshOps.validate
 exact (outer_roundtrip (NIL_Carriers.inner id) (unInner id) roundtrip _).symm.trans
   (congrArg (outer (unInner id)) (NJC_ValidatePort.source queries))

/-- SAME literal emitted resume body and all the retained reference operations,
with its validator occurrence now bound to the freshly emitted frozen child.
The remaining dictionary entries are not silently called native. -/
def resume (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (v : Fresh.V) (hash : H) :=
 NID_ResumeEmission.verifier.resume
 CheckpointBytes4Ops.ne CheckpointBytes4Ops.eq NIL_FreshOps.mapError NIL_FreshOps.any
 (fun x=>ok x) (ok (unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))
 (NIL_FreshOps.filled reserved) NIL_FreshOps.semantic NIL_FreshOps.weights
 NJC_ValidateEmission.verifier.validate_checkpoint_queries
 NIL_FreshOps.readK NIL_FreshOps.readE NIL_FreshOps.raw
 (fun v=>CheckpointBytes4Ops.checkpointSize (variant v))
 (fun v=>CheckpointBytes4Ops.finalLen (variant v))
 (fun v=>CheckpointBytes4Ops.tag (variant v)) (NIL_FreshOps.digest d)
 bytes proof public1 v hash

theorem reference (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (v : Fresh.V) (hash : H) :
 resume reserved d bytes proof public1 v hash=NIL_FreshOps.resume reserved d bytes proof public1 v hash := by
 have closed : NJC_ValidateEmission.verifier.validate_checkpoint_queries=NIL_FreshOps.validate :=
  funext clause
 unfold resume NIL_FreshOps.resume
 rw [closed]

theorem source (reserved : Bool) {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (hash : H) :
 NIL_StatePort.reply (resume reserved d bytes proof public1 .S2 hash)=
 AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) d bytes proof public1 .S2 hash := by
 rw [reference]
 exact NIY_ResumePort.source reserved d bytes proof public1 hash
#print axioms clause
#print axioms reference
#print axioms source
end NJC_ValidateCalls
