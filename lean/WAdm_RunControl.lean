import WAdm_Execution
import Tx1Q_Initial
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_RunControl
open Tx1Q_Carriers

/-- All64 flushed weights and next10 follow without parsing/model or primitive
arithmetic hypotheses. The row allocation comes from this run's pending call. -/
theorem fields {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : WAdm_Execution.Run installed reserved query geo D hash semantic pub proof split saved) :
    reserved = true ∧ split = 10#usize ∧ run.out.next.val = 10 ∧ run.flushed.val.length = 64 ∧
    ∀ x ∈ (slice k run.flushed).val, Port3_FlushInstall.Canonical x := by
  have init := Tx1Q_Initial.fields reserved (accumulator run.initial) run.initial_call
  have pend := Port3_NativePendingInstall.accepted_fields reserved
    (accumulator run.initial).weights.deref (pending run.pending) init.1 run.pending_call
  have native : Port3_NativeQueryBody.verifier.candidate.query_loop
      (Port3_NativeRowFrame.install (Tx1Q_QueryBridge.leaves query)) proof (prepared run.p)
      (accumulator run.initial) (arr e run.scratch) none (geometry run.geometry)
      (pending run.pending) 10#usize = ok (.Ok (accumulator run.out,pending run.after)) := run.query_call
  have frame := Port3_NativeQueryRaw.loop_raw (Tx1Q_QueryBridge.leaves query) proof (prepared run.p)
    (accumulator run.initial) (accumulator run.out) (arr e run.scratch) none (geometry run.geometry)
    (pending run.pending) (pending run.after) 10#usize init.1 pend.2.2.2 (by rw [init.2.1]; decide) native
  have size : (accumulator run.out).weights.val.length = 64 := by rw [frame.1]; exact init.1
  have lengths : (accumulator run.out).weights.deref.val.length ≤ (pending run.after).raw.val.length := by
    change (accumulator run.out).weights.val.length ≤ (pending run.after).raw.val.length
    rw [size,frame.2.1]
  have contents := Port3_FlushInstall.accepted_contents (pending run.after)
    (accumulator run.out).weights.deref (slice k run.flushed) lengths run.flush_call
  have canonical := Port3_FlushInstall.accepted_canonical (pending run.after)
    (accumulator run.out).weights.deref (slice k run.flushed) lengths run.flush_call
  refine ⟨pend.1,run.split_eq,frame.2.2,?_,canonical⟩
  have len := contents.2.trans size
  simpa only [slice,List.length_map] using len

#print axioms fields
end AspisR1.WAdm_RunControl
end
