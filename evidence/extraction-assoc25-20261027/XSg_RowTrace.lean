import XSg_RowTraceStep
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release
set_option autoImplicit false
noncomputable section
namespace XSg_RowTrace
open S7Kani3CallerTrace
/-- The complete actual row loop has one source-push history, obtained by the
generic loop induction and the SAME periodic cursor invariant. -/
theorem source (old : S8OwnedP6Finish.Weights) (v : alloc.vec.Vec aspis_core.field.QM31)
 (q : aspis_core.field.QM31) (i width : Usize) (basis : XSe_BasisUpdate.Basis)
 (before after : verifier.BatchedWeights) (canonical : XRp_PowersQAdd.CanonicalQ q)
 (bm : XSe_BasisUpdate.Canonical basis) (small : width.val≤256)
 (len : before.raw.val.length=width.val)
 (phase : ∀ row∈before.raw.val,XSg_RowPhase.Bound before.terms.val row)
 (history : ∃ sum,PushTrace old (XRu_PushTransport.bw before) sum)
 (run : verifier.accumulate_batched_with_node_loop1 {start:=0#usize,«end»:=width}
  v q i before width basis=ok after) :
 (∀ row∈after.raw.val,XSg_RowPhase.Bound (before.terms.val+1) row) ∧
 ∃ sum,PushTrace old (XRu_PushTransport.bw after) sum := by
 unfold verifier.accumulate_batched_with_node_loop1 at run
 apply XRl_LoopInvariant.preserve _
  (fun s => XSg_RowLoopPhase.Inv before.terms.val width.val s ∧
    ∃ sum,PushTrace old (XRu_PushTransport.bw s.2) sum)
  (fun b => (∀ row∈b.raw.val,XSg_RowPhase.Bound (before.terms.val+1) row) ∧
    ∃ sum,PushTrace old (XRu_PushTransport.bw b) sum)
  (fun s => XSc_RangeMeasure.remaining s.1) ?_
  ({start:=0#usize,«end»:=width},before) after ?_ run
 · intro s r inv hr
   rcases s with ⟨iter,b⟩
   have ph := XSg_RowLoopPhase.step v q i width basis before.terms.val canonical bm small (iter,b) r inv.1 hr
   have tr := XSg_RowTraceStep.source old v q i width basis before.terms.val (iter,b) r canonical bm small inv.1 inv.2 hr
   cases r with
   | done out => exact ⟨ph,tr⟩
   | cont next => exact ⟨⟨ph.1,tr⟩,ph.2⟩
 · exact ⟨⟨rfl,by change 0≤width.val;omega,len,rfl,XSg_Sweep.initial _ _ phase⟩,history⟩
#print axioms source
end XSg_RowTrace
