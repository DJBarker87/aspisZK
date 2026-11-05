import NIL_HeaderAny
import NIL_SectionPorts
import NIL_TryTransport
import NIL_AllocationPort
set_option autoImplicit false
noncomputable section
namespace NIL_SourceModel
open Aeneas Aeneas.Std Result NIL_Carriers NIL_StatePort
open NIL_ResultTransport NIL_ResultReverse NIL_TryTransport AspisR1

theorem source (reserved : Bool) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes proof public1 : Slice U8) (hash : H) :
 reply (NIL_FreshOps.resume reserved d bytes proof public1 .S2 hash)=
 AspisR1Stage2.verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) d
 bytes proof public1 .S2 hash := by
 have checkpoint : CheckpointBytes4Ops.checkpointSize .S2=ok 1768#usize := by rfl
 unfold NIL_FreshOps.resume NID_ResumeEmission.verifier.resume
 unfold AspisR1Stage2.verifier.resumeWithOps
 simp only [CheckpointBytes4Ops.ops,variant,checkpoint,bind_tc_ok]
 by_cases same : Slice.len bytes=1768#usize
 · rw [same]
   simp only [bne_self_eq_false,Bool.false_eq_true,if_false]
   simp only [NIL_StatePort.reply,outer_bind,bind_outer,outer_if,
    NIL_FreshOps.raw,NIL_FreshOps.readK,NIL_FreshOps.readE,
    NIL_FreshOps.semantic,NIL_FreshOps.weights,NIL_FreshOps.validate,
    NIL_HeaderAny.source]
   simp only [←NIL_TryTransport.fresh,←NIL_TryTransport.cohort,map_try,
    outer_bind,bind_outer,outer_if,reader_reverse,k_reverse,e_reverse]
 · have ne : (Slice.len bytes != 1768#usize)=true := by simpa only [bne_iff_ne] using same
   rw [ne]
   rfl
#print axioms source
end NIL_SourceModel
