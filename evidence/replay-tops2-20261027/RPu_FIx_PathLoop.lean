import RPu_FIx_PathLoopStep
import RPu_FIx_PathAlgebra
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_PathLoop
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIx_PathLoopStep (loop)
abbrev Range := core.ops.range.Range Usize

def model (selector bit : NQ) (a a1 : Array NQ 16#usize) :
    Nat → Nat → (Fin (17#usize).val → K) → (Fin (17#usize).val → K)
  | 0,_,old => old
  | n+1,lane,old => model selector bit a a1 n (lane+1) (FIx_PathAlgebra.step lane selector bit a a1 old)

theorem value (n : Nat) (r : Range) (selector bit : NQ) (a a1 : Array NQ 16#usize)
    (path out : Array NQ 17#usize) (hend : r.end.val=8) (span : r.start.val+n=8)
    (hs : Canon selector) (hb : Canon bit) (ha : canonical a) (ha1 : canonical a1) (hp : canonical path)
    (success : loop r selector a a1 bit path=ok out) :
    canonical out ∧ decoded out=model selector bit a a1 n r.start.val (decoded path) := by
  induction n generalizing r path with
  | zero =>
    rw [FIx_PathLoopStep.value,OccupancyRangeTraversal.next_done r (by omega),bind_tc_ok] at success
    have same : path=out := Result.ok.inj success
    subst out
    exact ⟨hp,rfl⟩
  | succ n ih =>
    obtain ⟨r',hn,hstart,he,hbound⟩ := OccupancyRangeTraversal.next_step r (by omega)
    rw [FIx_PathLoopStep.value,hn,bind_tc_ok] at success
    change (do let next←FIx_PathStep.run r.start selector a a1 bit path; loop r' selector a a1 bit next)=ok out at success
    obtain ⟨next,hnext,tail⟩ := FIv_Map.bind_success _ _ _ success
    have hl : r.start.val<8 := by omega
    have v := FIx_PathStep.value r.start selector bit a a1 path next hl hs hb ha ha1 hp hnext
    have rest := ih r' next (by rw [he];exact hend) (by omega) v.1 tail
    refine ⟨rest.1,?_⟩
    rw [rest.2,v.2,FIx_PathAlgebra.value,hstart]
    rfl
#print axioms value
end AspisR1.FIx_PathLoop
end
