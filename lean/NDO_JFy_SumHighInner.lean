import RPv_JFy_ArrayTotal
import RPu_FIq_Native10
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_SumHighInner
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
open pool_v1.pair_forest_semantic_terminal

theorem source (n : Nat) (iter : core.ops.range.Range Usize)
    (s : pool_v1.pair_forest_copy_terminal.Selectors) (acc : field.QM31)
    (he : iter.end.val≤64) (span : iter.start.val+n=iter.end.val)
    (hs : FIw_ArrayValue.canonical s.high) (hc : Canon acc) :
    ∃ out,sum_high_loop0_loop0 iter s acc=ok (s,out) ∧ Canon out := by
  induction n generalizing iter acc with
  | zero =>
    refine ⟨acc,?_,hc⟩
    rw [sum_high_loop0_loop0,OccupancyRangeTraversal.next_done iter (by omega),bind_tc_ok]
    rfl
  | succ n ih =>
    obtain ⟨next,hn,hstart,hend,_⟩ := OccupancyRangeTraversal.next_step iter (by omega)
    obtain ⟨q,hq,hqc⟩ := JFy_ArrayTotal.read s.high iter.start (by change iter.start.val<64;omega) hs
    obtain ⟨acc1,ha,hac,_⟩ := FIv_PreparedTotal.add acc q hc hqc
    obtain ⟨out,tail,hout⟩ := ih next acc1 (by rw [hend];exact he) (by rw [hend,hstart];omega) hac
    refine ⟨out,?_,hout⟩
    rw [sum_high_loop0_loop0,hn,bind_tc_ok]
    change (do let q ← Array.index_usize s.high iter.start
               let a ← field.QM31.add acc q
               sum_high_loop0_loop0 next s a)=ok (s,out)
    rw [hq,bind_tc_ok,ha,bind_tc_ok,tail]
#print axioms source
end AspisR1.JFy_SumHighInner
end
