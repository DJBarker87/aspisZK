import RPu_FIy_OccupancyLoopStep
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_OccupancyLoop
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIy_OccupancyLoopStep (loop)
abbrev Range := core.ops.range.Range Usize

def model (a : Array NQ 16#usize) (m b : NQ) :
    Nat → Nat → (Fin (12#usize).val → K) → (Fin (12#usize).val → K)
  | 0,_,old=>old
  | n+1,lane,old=>model a m b n (lane+1) (FIy_OccupancyStep.model lane a m b old)

theorem value (n : Nat) (r : Range) (a : Array NQ 16#usize) (m b : NQ)
    (o out : Array NQ 12#usize) (hend : r.end.val=8) (span : r.start.val+n=8)
    (ha : canonical a) (hm : Canon m) (hb : Canon b) (ho : canonical o)
    (success : loop r a m o b=ok out) :
    canonical out ∧ decoded out=model a m b n r.start.val (decoded o) := by
  induction n generalizing r o with
  | zero=>
    rw [FIy_OccupancyLoopStep.value,OccupancyRangeTraversal.next_done r (by omega),bind_tc_ok] at success
    have same : o=out := Result.ok.inj success
    subst out
    exact ⟨ho,rfl⟩
  | succ n ih=>
    obtain ⟨r',hn,hstart,he,hbound⟩ := OccupancyRangeTraversal.next_step r (by omega)
    rw [FIy_OccupancyLoopStep.value,hn,bind_tc_ok] at success
    change (do let next←FIy_OccupancyStep.run r.start a m b o; loop r' a m next b)=ok out at success
    obtain ⟨next,hnext,tail⟩ := FIv_Map.bind_success _ _ _ success
    have hl : r.start.val<8 := by omega
    have v := FIy_OccupancyStep.value r.start a m b o next hl ha hm hb ho hnext
    have rest := ih r' next (by rw [he];exact hend) (by omega) v.1 tail
    refine ⟨rest.1,?_⟩
    rw [rest.2,v.2,hstart]
    rfl
#print axioms value
end AspisR1.FIy_OccupancyLoop
end
