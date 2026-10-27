import RPu_FIy_DigestLoopStep
import OccupancyRangeTraversal
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_DigestLoop
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
open FIw_ArrayValue (canonical decoded)
open FIy_DigestLoopStep (loop)
abbrev Range := core.ops.range.Range Usize

def model (selector : NQ) (opened : Array NQ 16#usize) (start : Nat)
    (expected : Array U32 8#usize) (right : Bool) :
    Nat → Nat → (Fin (8#usize).val → K) → (Fin (8#usize).val → K)
  | 0,_,old=>old
  | n+1,lane,old=>model selector opened start expected right n (lane+1)
      (FIy_DigestLane.model lane selector opened start expected right old)

theorem value (n : Nat) (r : Range) (output out : Array NQ 8#usize)
    (selector : NQ) (opened : Array NQ 16#usize) (start : Usize)
    (expected : Array U32 8#usize) (right : Bool)
    (hend : r.end.val=8) (span : r.start.val+n=8) (hb : start.val+8≤16)
    (ho : canonical output) (hs : Canon selector) (ha : canonical opened)
    (he : ∀ x∈expected.val,x.val<FIw_ScalarArithmetic.P)
    (success : loop r output selector opened start expected right=ok out) :
    canonical out ∧ decoded out=model selector opened start.val expected right n r.start.val (decoded output) := by
  induction n generalizing r output with
  | zero=>
    rw [FIy_DigestLoopStep.value,OccupancyRangeTraversal.next_done r (by omega),bind_tc_ok] at success
    have same : output=out := Result.ok.inj success
    subst out
    exact ⟨ho,rfl⟩
  | succ n ih=>
    obtain ⟨r',hn,hstart,heq,hbound⟩ := OccupancyRangeTraversal.next_step r (by omega)
    rw [FIy_DigestLoopStep.value,hn,bind_tc_ok] at success
    change (do let next←FIy_DigestLane.run r.start output selector opened start expected right
               loop r' next selector opened start expected right)=ok out at success
    obtain ⟨next,hnext,tail⟩ := FIv_Map.bind_success _ _ _ success
    have hl : r.start.val<8 := by omega
    have v := FIy_DigestLane.value r.start start output next selector opened expected right hl hb ho hs ha he hnext
    have rest := ih r' next (by rw [heq];exact hend) (by omega) v.1 tail
    refine ⟨rest.1,?_⟩
    rw [rest.2,v.2,hstart]
    rfl
#print axioms value
end AspisR1.FIy_DigestLoop
end
