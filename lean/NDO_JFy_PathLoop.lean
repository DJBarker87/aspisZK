import NDO_JFy_PathStep
import RPv_FIx_PathLoopStep
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PathLoop
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open FIx_PathLoopStep (loop)

theorem source (n : Nat) (r : core.ops.range.Range Usize) (selector bit : field.QM31)
    (a b : Array field.QM31 16#usize) (path : Array field.QM31 17#usize)
    (he : r.end.val≤8) (span : r.start.val+n=r.end.val)
    (hs : Canon selector) (hb : Canon bit) (ha : canonical a) (hbb : canonical b) (hp : canonical path) :
    ∃ out,loop r selector a b bit path=ok out ∧ canonical out := by
  induction n generalizing r path with
  | zero =>
    refine ⟨path,?_,hp⟩
    rw [FIx_PathLoopStep.value,OccupancyRangeTraversal.next_done r (by omega),bind_tc_ok]
    rfl
  | succ n ih =>
    obtain ⟨r',hn,hs',he',_⟩ := OccupancyRangeTraversal.next_step r (by omega)
    obtain ⟨next,call,hnext⟩ := WP.spec_imp_exists (JFy_PathStep.source r.start selector bit a b path (by omega) hs hb ha hbb hp)
    obtain ⟨out,tail,hout⟩ := ih r' next (by rw [he'];exact he) (by rw [he',hs'];omega) hnext
    refine ⟨out,?_,hout⟩
    rw [FIx_PathLoopStep.value,hn,bind_tc_ok]
    change (do let p ← FIx_PathStep.run r.start selector a b bit path
               loop r' selector a b bit p)=ok out
    rw [call,bind_tc_ok,tail]
#print axioms source

@[step] theorem full (selector bit : field.QM31) (a b : Array field.QM31 16#usize) (path : Array field.QM31 17#usize)
    (hs : Canon selector) (hb : Canon bit) (ha : canonical a) (hbb : canonical b) (hp : canonical path) :
    loop {start:=0#usize,«end»:=8#usize} selector a b bit path ⦃ out => canonical out ⦄ := by
  apply exists_imp_spec
  exact source 8 _ selector bit a b path (by decide) rfl hs hb ha hbb hp
#print axioms full
end AspisR1.JFy_PathLoop
end
