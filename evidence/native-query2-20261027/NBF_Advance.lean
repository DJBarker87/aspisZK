import NBF_RowShape
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_Advance
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)
/-- The SAME accepted accumulation tail advances both counters and preserves
whole-vector phase progress. No next-phase premise is supplied by a caller. -/
theorem accepted (ops : Ops) (p : verifier.Prepared) (a out : verifier.Accumulator)
 (node : U32) (value : Stage2E) (b bout : verifier.BatchedWeights)
 (size : a.weights.val.length=64) (nextBound : a.next.val<10)
 (sync : b.terms=a.next)
 (progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b))
 (hq : ∀ k, (S7Kani2OwnedRowRefinement.powerLimb (Port3_RowsInstall.toK a.power) k).val<2^31-1)
 (run : verifier.accumulate_batched_with_node (NBF_Accumulate.install ops)
   p a node value b=ok (out,bout)) :
 out.weights=a.weights ∧ out.next.val=a.next.val+1 ∧ bout.terms=out.next ∧
 S7JoinRowsTrace.Progress out.next.val 0 (Port3_RowsInstall.toBW bout) := by
 obtain ⟨basis,mid,hbasis,hrows,terms,len,phase,body⟩ := NBF_Accumulate.rows
   ops p a node value b size progress hq
 rw [body] at run
 simp only [lift,bind_tc_ok] at run
 obtain ⟨product,hproduct,run⟩ := bind_success _ _ _ run
 obtain ⟨rhs,hrhs,run⟩ := bind_success _ _ _ run
 obtain ⟨marked,hmarked,run⟩ := bind_success _ _ _ run
 obtain ⟨power,hpower,run⟩ := bind_success _ _ _ run
 cases Result.ok.inj run
 have next : (Usize.wrapping_add a.next 1#usize).val=a.next.val+1 :=
   Port3_Wrapping.increment a.next (by omega)
 have counter : Usize.wrapping_add mid.terms 1#usize=Usize.wrapping_add a.next 1#usize := by
   rw [terms,sync]
 refine ⟨rfl,next,counter,?_⟩
 apply NBF_RowShape.progress
 · exact congrArg UScalar.val counter
 · exact len
 · intro j row get
   have actual := phase j row get
   change NBB_Sweep.Bound (Usize.wrapping_add a.next 1#usize).val row
   rw [next]
   have same : b.terms.val=a.next.val := congrArg UScalar.val sync
   rw [same] at actual
   exact actual
#print axioms accepted
end NBF_Advance
