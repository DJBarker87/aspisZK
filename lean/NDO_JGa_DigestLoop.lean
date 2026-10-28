import NDO_JGa_DigestLane
import RPv_FIy_DigestLoopStep
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_DigestLoop
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open FIy_DigestLoopStep (loop)

theorem source (n : Nat) (r : core.ops.range.Range Usize) (output : Array field.QM31 8#usize)
    (selector : field.QM31) (opened : Array field.QM31 16#usize) (start : Usize)
    (expected : Array U32 8#usize) (right : Bool) (hend : r.end.val=8) (span : r.start.val+n=8)
    (hb : start.val+8≤16) (ho : canonical output) (hs : Canon selector) (ha : canonical opened)
    (he : ∀ x∈expected.val,x.val<FIw_ScalarArithmetic.P) :
    ∃ out,loop r output selector opened start expected right=ok out ∧ canonical out := by
  induction n generalizing r output with
  | zero =>
    refine ⟨output,?_,ho⟩
    rw [FIy_DigestLoopStep.value,OccupancyRangeTraversal.next_done r (by omega),bind_tc_ok]
    rfl
  | succ n ih =>
    obtain ⟨r',hn,hs',he',_⟩ := OccupancyRangeTraversal.next_step r (by omega)
    obtain ⟨next,call,hnext⟩ := WP.spec_imp_exists (JGa_DigestLane.source r.start output selector opened start expected right (by omega) hb ho hs ha he)
    obtain ⟨out,tail,hout⟩ := ih r' next (by rw [he'];exact hend) (by omega) hnext
    refine ⟨out,?_,hout⟩
    rw [FIy_DigestLoopStep.value,hn,bind_tc_ok]
    change (do let next ← FIy_DigestLane.run r.start output selector opened start expected right; loop r' next selector opened start expected right)=ok out
    rw [call,bind_tc_ok,tail]
#print axioms source

@[step] theorem full (output : Array field.QM31 8#usize) (selector : field.QM31)
    (opened : Array field.QM31 16#usize) (start : Usize) (expected : Array U32 8#usize) (right : Bool)
    (hb : start.val+8≤16) (ho : canonical output) (hs : Canon selector) (ha : canonical opened)
    (he : ∀ x∈expected.val,x.val<FIw_ScalarArithmetic.P) :
    pool_v1.pair_forest_semantic_terminal.add_digest_binding output selector opened start expected right ⦃ out => canonical out ⦄ := by
  apply exists_imp_spec
  unfold pool_v1.pair_forest_semantic_terminal.add_digest_binding
  exact source 8 _ output selector opened start expected right (by rw [poseidon2.DIGEST_ELEMS];rfl) rfl hb ho hs ha he
#print axioms full
end AspisR1.JGa_DigestLoop
end
