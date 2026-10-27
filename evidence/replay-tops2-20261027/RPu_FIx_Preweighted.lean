import RPu_FIx_PreweightedLoop
import RPu_FIx_WordArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_Preweighted
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)

def count (start length : Nat) : Nat := (start+length-1)/4-start/4+1

theorem value {N : Usize} (packed out : Array NQ 24#usize) (start : Usize) (a : Array NQ N)
    (positive : 0<N.val) (interval : start.val+N.val≤96)
    (hp : canonical packed) (ha : canonical a)
    (success : pool_v1.pair_forest_semantic_terminal.add_preweighted packed start a=ok out) :
    canonical out ∧ decoded out=FIx_PreweightedLoop.model a start.val
      (count start.val N.val) (start.val/4) (decoded packed) := by
  unfold pool_v1.pair_forest_semantic_terminal.add_preweighted at success
  obtain ⟨first,hfirst,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨endpoint,hendpoint,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨endMinusOne,hendMinusOne,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨last,hlast,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨r,hr,success⟩ := FIv_Map.bind_success _ _ _ success
  have firstValue := FIx_WordArithmetic.div start 4#usize first (by decide) hfirst
  have endpointValue := FIw_WordValue.add start N endpoint hendpoint
  have endValue := FIx_WordArithmetic.sub endpoint 1#usize endMinusOne (by rw [endpointValue];scalar_tac) hendMinusOne
  have lastValue := FIx_WordArithmetic.div endMinusOne 4#usize last (by decide) hlast
  have r_same : r={start:=first,«end»:=last,exhausted:=false} := (Result.ok.inj hr).symm
  subst r
  have lastBound : last.val<24 := by
    rw [lastValue,endValue,endpointValue]
    change (start.val+N.val-1)/4<24
    omega
  have ascending : first.val≤last.val := by
    rw [firstValue,lastValue,endValue,endpointValue]
    change start.val/4≤(start.val+N.val-1)/4
    omega
  have result := FIx_PreweightedLoop.value _ packed out start a lastBound hp ha success
  refine ⟨result.1,?_⟩
  rw [result.2]
  have remain : FIx_PreweightedLoop.remaining {start:=first,«end»:=last,exhausted:=false}=count start.val N.val := by
    unfold FIx_PreweightedLoop.remaining count
    simp only [Bool.false_eq_true,false_or]
    rw [if_neg (by omega),firstValue,lastValue,endValue,endpointValue]
    rfl
  rw [remain,firstValue]
  rfl
#print axioms value
end AspisR1.FIx_Preweighted
end
