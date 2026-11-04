import NBF_RowShape
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFP_Advance
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody Port3_PushFrame
/-- Independent global/local counters cover both TX1 and resumed TX2. The
row phase comes from the SAME actual accumulation, without a sync premise. -/
theorem accepted (ops : Ops) (p : verifier.Prepared) (a out : verifier.Accumulator)
 (node : U32) (value : Stage2E) (b bout : verifier.BatchedWeights)
 (size : a.weights.val.length=64) (global : a.next.val<22) (localActive : b.terms.val<22)
 (progress : S7JoinRowsTrace.Progress b.terms.val 0 (Port3_RowsInstall.toBW b))
 (power : NBF_PowerStep.Canonical a.power)
 (run : verifier.accumulate_batched_with_node (NBF_Accumulate.install ops)
   p a node value b=ok (out,bout)) :
 out.weights=a.weights ∧ out.next.val=a.next.val+1 ∧ bout.terms.val=b.terms.val+1 ∧
 S7JoinRowsTrace.Progress bout.terms.val 0 (Port3_RowsInstall.toBW bout) := by
 obtain ⟨basis,mid,hbasis,hrows,terms,len,phase,body⟩ := NBF_Accumulate.rows
  ops p a node value b size progress power
 rw [body] at run
 simp only [lift,bind_tc_ok] at run
 obtain ⟨product,hproduct,run⟩ := bind_success _ _ _ run
 obtain ⟨rhs,hrhs,run⟩ := bind_success _ _ _ run
 obtain ⟨marked,hmarked,run⟩ := bind_success _ _ _ run
 obtain ⟨newpower,hpower,run⟩ := bind_success _ _ _ run
 cases Result.ok.inj run
 have next := Port3_Wrapping.increment a.next (by omega)
 have counter : (Usize.wrapping_add mid.terms 1#usize).val=b.terms.val+1 := by
  rw [terms]
  exact Port3_Wrapping.increment b.terms (by omega)
 refine ⟨rfl,next,counter,?_⟩
 apply NBF_RowShape.progress
 · rfl
 · exact len
 · intro j row get
   change NBB_Sweep.Bound (Usize.wrapping_add mid.terms 1#usize).val row
   rw [counter]
   exact phase j row get
#print axioms accepted
end AspisR1.NFP_Advance
end
