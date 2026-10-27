import XSg_RowLoopPhase
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release
set_option autoImplicit false
namespace XSg_RowLoop
/-- The whole actual row loop advances every row exactly one periodic phase.
The generic source loop invariant supplies induction; no rows are unrolled. -/
theorem source (v : alloc.vec.Vec aspis_core.field.QM31) (q : aspis_core.field.QM31)
 (i width : Usize) (basis : XSe_BasisUpdate.Basis) (before after : verifier.BatchedWeights)
 (canon : XRp_PowersQAdd.CanonicalQ q) (bm : XSe_BasisUpdate.Canonical basis)
 (small : width.val≤256) (len : before.raw.val.length=width.val)
 (phase : ∀ row∈before.raw.val,XSg_RowPhase.Bound before.terms.val row)
 (run : verifier.accumulate_batched_with_node_loop1 {start:=0#usize,«end»:=width}
  v q i before width basis=ok after) :
 ∀ row∈after.raw.val,XSg_RowPhase.Bound (before.terms.val+1) row := by
 unfold verifier.accumulate_batched_with_node_loop1 at run
 apply XRl_LoopInvariant.preserve _ (XSg_RowLoopPhase.Inv before.terms.val width.val)
  (fun b => ∀ row∈b.raw.val,XSg_RowPhase.Bound (before.terms.val+1) row)
  (fun s => XSc_RangeMeasure.remaining s.1)
  (by
   intro s r inv hr
   rcases s with ⟨iter,b⟩
   exact XSg_RowLoopPhase.step v q i width basis before.terms.val canon bm small (iter,b) r inv hr)
  ({start:=0#usize,«end»:=width},before) after ?_ run
 exact ⟨rfl,by change 0≤width.val;omega,len,rfl,XSg_Sweep.initial _ _ phase⟩
#print axioms source
end XSg_RowLoop
