import NDO_JGa_FrontierStep
import RPv_FIy_FrontierLoopStep
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_FrontierLoop
open Aeneas Aeneas.Std Result WP FIq_Native
open FIw_ArrayValue (canonical)
open FIy_FrontierStep (Selectors Snapshot)
open FIy_FrontierLoopStep (loop)

theorem source (n : Nat) (r : core.ops.range.Range Usize) (a : Array field.QM31 16#usize)
    (s : Selectors) (d : Array field.QM31 8#usize) (src : Snapshot)
    (he : r.end.val=20) (span : r.start.val+n=20) (ha : canonical a) (hd : canonical d)
    (hh : canonical s.high) (hl : canonical s.low)
    (hf : ∀ row∈src.frontier.val,∀ x∈row.val,x.val<FIw_ScalarArithmetic.P) :
    ∃ out,loop r a s d src=ok (out,src) ∧ canonical out := by
  induction n generalizing r d with
  | zero =>
    refine ⟨d,?_,hd⟩
    rw [FIy_FrontierLoopStep.value,OccupancyRangeTraversal.next_done r (by omega),bind_tc_ok]
    rfl
  | succ n ih =>
    obtain ⟨r',hn,hs',he',_⟩ := OccupancyRangeTraversal.next_step r (by omega)
    obtain ⟨next,call,hnext⟩ := WP.spec_imp_exists (JGa_FrontierStep.source r.start a s d src (by omega) ha hd hh hl hf)
    obtain ⟨out,tail,hout⟩ := ih r' next (by rw [he'];exact he) (by omega) hnext
    refine ⟨out,?_,hout⟩
    rw [FIy_FrontierLoopStep.value,hn,bind_tc_ok]
    change (do let next ← FIy_FrontierStep.run r.start a s d src; loop r' a s next src)=ok (out,src)
    rw [call,bind_tc_ok,tail]
#print axioms source
end AspisR1.JGa_FrontierLoop
end
