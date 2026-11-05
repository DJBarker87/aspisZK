import NIL_ResumeComposition
import NIL_PortBind
import NIL_SectionPorts
import NIL_AllocationPort
set_option autoImplicit false
noncomputable section
namespace NIL_TailPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1

/-- Candidate for the exact unresolved tail port, without an acceptance premise. -/
theorem source (reserved : Bool) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8) (end1 : Usize) (next : U8) :
 NIL_StatePort.reply (NIL_ResumeSplit.tail reserved d bytes .S2 end1 next)=
 NIL_ResumeCohortTail.tail (CheckpointBytes4Ops.ops reserved) bytes .S2 end1 next := by
 unfold NIL_ResumeSplit.tail NIL_ResumeTailCut.tail NIL_ResumeCohortTail.tail NIL_StatePort.reply
 simp only [NIL_FreshOps.raw,CheckpointBytes4Ops.ops,outer_bind,bind_outer,
   NIL_ResultCases.outer_prodlet,NIL_ResultCases.outer_ok]
#print axioms source
end NIL_TailPort
