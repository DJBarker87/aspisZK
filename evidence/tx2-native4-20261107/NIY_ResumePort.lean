import NIY_TailPort
set_option autoImplicit false
noncomputable section
namespace NIY_ResumePort
open Aeneas Aeneas.Std Result NIL_Carriers AspisR1

/-- Discharge NIL's tail-interface premise for the exact fresh reference resume.
Actual native primitive/source installation and caller domains remain distinct. -/
theorem source (reserved : Bool) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (hash : H) :
 NIL_StatePort.reply (NIL_FreshOps.resume reserved d bytes proof public1 .S2 hash)=
 AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) d bytes proof public1 .S2 hash := by
 apply NIL_ResumeComposition.source
 intro end1 next
 exact NIY_TailPort.source reserved d bytes end1 next
#print axioms source
end NIY_ResumePort
