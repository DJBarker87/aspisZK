import FIy_FrontierMeaning
import FIy_FrontierFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIy_FrontierLoop
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FIy_FrontierStep (Snapshot Selectors)
open FIy_FrontierLoopStep (loop)
abbrev Range := core.ops.range.Range Usize

def model (src : Snapshot) (s : Selectors) (a : Array NQ 16#usize) :
    Nat → Nat → (Fin (8#usize).val → K) → (Fin (8#usize).val → K)
  | 0,_,old=>old
  | n+1,level,old=>model src s a n (level+1) (fun j=>old j+FIy_FrontierMeaning.increment src s a level j.val)

theorem value (n : Nat) (r : Range) (a : Array NQ 16#usize) (s : Selectors)
    (d out : Array NQ 8#usize) (src returned : Snapshot)
    (hend : r.end.val=20) (span : r.start.val+n=20)
    (ha : canonical a) (hh : canonical s.high) (hl : canonical s.low) (hd : canonical d)
    (hf : ∀ row∈src.frontier.val,∀ x∈row.val,x.val<FIw_ScalarArithmetic.P)
    (success : loop r a s d src=ok (out,returned)) :
    returned=src ∧ canonical out ∧ decoded out=model src s a n r.start.val (decoded d) := by
  induction n generalizing r d with
  | zero=>
    rw [FIy_FrontierLoopStep.value,OccupancyRangeTraversal.next_done r (by omega),bind_tc_ok] at success
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Result.ok.inj success)
    exact ⟨rfl,hd,rfl⟩
  | succ n ih=>
    obtain ⟨r',hn,hstart,he,hbound⟩ := OccupancyRangeTraversal.next_step r (by omega)
    rw [FIy_FrontierLoopStep.value,hn,bind_tc_ok] at success
    change (do let next←FIy_FrontierStep.run r.start a s d src;loop r' a s next src)=ok (out,returned) at success
    obtain ⟨next,hnext,tail⟩ := FIv_Map.bind_success _ _ _ success
    have one := FIy_FrontierMeaning.value r.start a s d next src (by omega) ha hh hl hd hf hnext
    have rest := ih r' next (by rw [he];exact hend) (by omega) one.1 tail
    refine ⟨rest.1,rest.2.1,?_⟩
    rw [rest.2.2,hstart]
    have same : decoded next=fun j=>decoded d j+FIy_FrontierMeaning.increment src s a r.start.val j.val := funext one.2
    rw [same]
    rfl
#print axioms value
end AspisR1.FIy_FrontierLoop
end
