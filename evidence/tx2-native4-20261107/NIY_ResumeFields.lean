import NIY_ResumePort
set_option autoImplicit false
noncomputable section
namespace NIY_ResumeFields
open Aeneas Aeneas.Std Result NIL_Carriers AspisR1

/-- Fields are derived from the SAME fresh-reference returned pair, rather than
an independently selected cohort success. This is not native caller installation. -/
theorem fields (reserved : Bool) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (hash : H)
 (p : NIL_StatePort.F.P) (a : NIL_StatePort.F.A)
 (run : NIL_FreshOps.resume reserved d bytes proof public1 .S2 hash=ok (.Ok (p,a))) :
 Nonempty (OraclePortCkptAbiSourceFields.Fields (CheckpointBytes4Ops.ops reserved)
   bytes .S2 (NIL_StatePort.prepared p) (NIL_StatePort.accumulator a)) := by
 have same : AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
   d bytes proof public1 .S2 hash=
   ok (.Ok (NIL_StatePort.prepared p,NIL_StatePort.accumulator a)) := by
  rw [←NIY_ResumePort.source,run]
  rfl
 exact CheckpointBytes4Ops.successful_fields reserved d bytes proof public1 .S2 hash
   (NIL_StatePort.prepared p) (NIL_StatePort.accumulator a) same

/-- The same returning pair forces the reference reservation branch to succeed;
no allocation availability assumption or independently chosen run is introduced. -/
theorem reservation (reserved : Bool) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (hash : H)
 (p : NIL_StatePort.F.P) (a : NIL_StatePort.F.A)
 (run : NIL_FreshOps.resume reserved d bytes proof public1 .S2 hash=ok (.Ok (p,a))) :
 reserved=true := by
 have same : AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved)
   d bytes proof public1 .S2 hash=
   ok (.Ok (NIL_StatePort.prepared p,NIL_StatePort.accumulator a)) := by
  rw [←NIY_ResumePort.source,run]
  rfl
 exact CheckpointBytes4Ops.successful_reservation reserved d bytes proof public1 .S2 hash
   (NIL_StatePort.prepared p) (NIL_StatePort.accumulator a) same
#print axioms fields
#print axioms reservation
end NIY_ResumeFields
