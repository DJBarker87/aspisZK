import NJC_ValidateStep
import NIL_Carriers
import NJC_ClosedCalls
set_option autoImplicit false
noncomputable section
namespace NJC_ValidatePort
open Aeneas Aeneas.Std Result ControlFlow AspisR1
abbrev E := NID_ResumeEmission.verifier.Error

def pending : core.result.Result Unit AspisR1Stage2.verifier.Error →
 Option (core.result.Result Unit E)
 | .Ok _ => some (.Ok ())
 | .Err _ => none

/-- Finite induction on the entered suffix of the freshly emitted frozen
validator. Every iteration uses the SAME full prefix and actual array22.
This includes every duplicate/range rejection, without acceptance premises. -/
theorem loop_exact (q : Array U32 22#usize) (pre tail : List U32) (i : Usize)
 (shape : q.val=pre++tail) (index : i.val=pre.length) :
 NJC_ValidateEmission.verifier.validate_checkpoint_queries_loop q i=
 ok (pending (CheckpointBytes4Ops.queryLoop pre tail)) := by
 induction tail generalizing pre i with
 | nil =>
  have inactive : ¬i<Slice.len (Array.to_slice q) := by
   change ¬i.val<q.val.length
   rw [shape,index,List.append_nil]
   omega
  unfold NJC_ValidateEmission.verifier.validate_checkpoint_queries_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,NJC_ValidateEmission.verifier.validate_checkpoint_queries_loop.body,
   lift,bind_tc_ok,if_neg inactive,CheckpointBytes4Ops.queryLoop,pending]
 | cons x tail ih =>
  have step:=NJC_ValidateStep.source q i pre tail x shape index
  unfold NJC_ValidateEmission.verifier.validate_checkpoint_queries_loop
  rw [Aeneas.Std.loop.eq_def]
  simp only [Aeneas.Std.uncurry,step]
  by_cases bad : x.val≥262144 ∨ x∈pre
  · simp only [if_pos bad,CheckpointBytes4Ops.queryLoop,pending]
  · simp only [if_neg bad,CheckpointBytes4Ops.queryLoop]
    have small : i.val<22 := by
     have size : q.val.length=22 := q.property
     rw [shape,List.length_append,List.length_cons] at size
     omega
    have next : (Usize.wrapping_add i 1#usize).val=(pre++[x]).length := by
     rw [Port3_Wrapping.increment i (by omega),index,List.length_append,List.length_singleton]
    have shape1 : q.val=(pre++[x])++tail := by
     simpa only [List.append_assoc,List.singleton_append] using shape
    exact ih (pre++[x]) (Usize.wrapping_add i 1#usize) shape1 next

/-- Complete fresh frozen-validator Result to the cohort at the SAME array.
The nominal error mapping preserves Checkpoint, all other inner error tags,
and outer fail/div; the finite loop itself is proved total. -/
theorem source (queries : Array U32 22#usize) :
 NIL_Carriers.outer (NIL_Carriers.inner id)
  (NJC_ValidateEmission.verifier.validate_checkpoint_queries queries)=
 CheckpointBytes4Ops.validate queries := by
 unfold NJC_ValidateEmission.verifier.validate_checkpoint_queries CheckpointBytes4Ops.validate
 rw [loop_exact queries [] queries.val 0#usize rfl rfl,bind_tc_ok]
 rcases Port5Q2_ReaderValidate.query_result [] queries.val with good|bad
 · rw [good];rfl
 · rw [bad];rfl

/-- No state/oracle event is silently dropped: the pure child's full Result
transport commutes with an unchanged caller state and an empty effect trace. -/
theorem frame {S Event : Type} (state : S) (queries : Array U32 22#usize) :
 NEB_PureFrame.run (Event:=Event) state
  (NIL_Carriers.outer (NIL_Carriers.inner id)
    (NJC_ValidateEmission.verifier.validate_checkpoint_queries queries))=
 NEB_PureFrame.run state (CheckpointBytes4Ops.validate queries) := by
 rw [source]
#print axioms loop_exact
#print axioms source
#print axioms frame
end NJC_ValidatePort
