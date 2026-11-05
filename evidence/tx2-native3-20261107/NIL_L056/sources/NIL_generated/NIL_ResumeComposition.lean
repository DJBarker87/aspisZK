import NIL_ResumeSplit
import NIL_CohortSplit
import NIL_ResumePrefixPort
set_option autoImplicit false
noncomputable section
namespace NIL_ResumeComposition
open Aeneas Aeneas.Std Result NIL_Carriers AspisR1

/-- Exact remaining tail interface; this theorem does not discharge that interface. -/
theorem source (reserved : Bool) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (bytes proof public1 : Slice U8) (hash : H)
 (tail : ∀ end1 next,NIL_StatePort.reply
   (NIL_ResumeSplit.tail reserved d bytes .S2 end1 next)=
   NIL_ResumeCohortTail.tail (CheckpointBytes4Ops.ops reserved) bytes .S2 end1 next) :
 NIL_StatePort.reply (NIL_FreshOps.resume reserved d bytes proof public1 .S2 hash)=
 AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) d bytes proof public1 .S2 hash := by
 rw [NIL_ResumeSplit.source,NIL_CohortSplit.source]
 exact NIL_ResumePrefixPort.source NIL_StatePort.pair d bytes proof public1 hash reserved _ _ tail
#print axioms source
end NIL_ResumeComposition
