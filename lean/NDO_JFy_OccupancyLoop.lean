import RPv_JFy_Steps
import RPv_FIy_OccupancyLoopStep
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_OccupancyLoop
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open FIy_OccupancyLoopStep (loop)

@[step] theorem cell (lane : Usize) (a : Array field.QM31 16#usize) (m b : field.QM31)
    (occupancy : Array field.QM31 12#usize) (hl : lane.val<8) (ha : canonical a)
    (hm : Canon m) (hb : Canon b) (hc : canonical occupancy) :
    FIy_OccupancyStep.run lane a m b occupancy ⦃ out => canonical out ⦄ := by
  unfold FIy_OccupancyStep.run
  step* <;> first | assumption | scalar_tac
#print axioms cell

theorem source (n : Nat) (r : core.ops.range.Range Usize) (oneMinus both : field.QM31)
    (a : Array field.QM31 16#usize) (path : Array field.QM31 12#usize)
    (he : r.end.val≤8) (span : r.start.val+n=r.end.val)
    (hs : Canon oneMinus) (hb : Canon both) (ha : canonical a) (hp : canonical path) :
    ∃ out,loop r a oneMinus path both=ok out ∧ canonical out := by
  induction n generalizing r path with
  | zero =>
    refine ⟨path,?_,hp⟩
    rw [FIy_OccupancyLoopStep.value,OccupancyRangeTraversal.next_done r (by omega),bind_tc_ok]
    rfl
  | succ n ih =>
    obtain ⟨r',hn,hs',he',_⟩ := OccupancyRangeTraversal.next_step r (by omega)
    obtain ⟨next,call,hnext⟩ := WP.spec_imp_exists (cell r.start a oneMinus both path (by omega) ha hs hb hp)
    obtain ⟨out,tail,hout⟩ := ih r' next (by rw [he'];exact he) (by rw [he',hs'];omega) hnext
    refine ⟨out,?_,hout⟩
    rw [FIy_OccupancyLoopStep.value,hn,bind_tc_ok]
    change (do let p ← FIy_OccupancyStep.run r.start a oneMinus both path
               loop r' a oneMinus p both)=ok out
    rw [call,bind_tc_ok,tail]
#print axioms source
@[step] theorem full (a : Array field.QM31 16#usize) (m b : field.QM31) (path : Array field.QM31 12#usize)
    (ha : canonical a) (hm : Canon m) (hb : Canon b) (hp : canonical path) :
    loop {start:=0#usize,«end»:=8#usize} a m path b ⦃ out => canonical out ⦄ := by
  apply exists_imp_spec
  exact source 8 _ m b a path (by decide) rfl hm hb ha hp
#print axioms full
end AspisR1.JFy_OccupancyLoop
end
