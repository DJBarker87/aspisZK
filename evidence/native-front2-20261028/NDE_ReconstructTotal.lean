import NDE_LinearSteps
import NDE_RowBridge
import RPv_FIx_ArithmeticTotal
import RPv_FIx_ReconstructMeaning
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NDE_ReconstructTotal
open AspisR1
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIx_ReconstructStep (Capture callback)
open FIx_ReconstructTraversal (fold slice)

theorem fold_total (xs : List NQ) (bound : xs.length ≤ Usize.max) (acc : NQ) (c : Capture)
    (hc : ∀ x ∈ xs, Canon x) (ha : Canon acc) :
    ∃ out, fold ⟨slice xs bound,0⟩ acc c = ok out ∧ Canon out := by
  induction xs using List.reverseRecOn generalizing acc with
  | nil => exact ⟨acc,FIx_ReconstructTraversal.nil acc c,ha⟩
  | append_singleton xs x ih =>
    have hx := hc x (by simp)
    obtain ⟨double,hd,hcd,_⟩ := FIx_ArithmeticTotal.add acc acc ha ha
    obtain ⟨next,hn,hcn,_⟩ := FIx_ArithmeticTotal.add double x hcd hx
    have step : callback.call_mut c (acc,x) = ok (next,c) := by
      change (do let q ← FIq_Native.field.QM31.add acc acc
                 let q1 ← FIq_Native.field.QM31.add q x
                 ok (q1,c)) = ok (next,c)
      rw [hd,bind_tc_ok,hn,bind_tc_ok]
    obtain ⟨out,run,hco⟩ := ih (by simp only [List.length_append,List.length_singleton] at bound; omega)
      next (by intro y hy; exact hc y (by simp [hy])) hcn
    refine ⟨out,?_,hco⟩
    rw [FIx_ReconstructTraversal.append,step,bind_tc_ok]
    exact run

theorem source (view : Array NQ 16#usize) (hc : ∀ x ∈ view.val, Canon x) :
    ∃ out, FIq_Native.pool_v1.pair_forest_semantic_terminal.reconstruct_10 view = ok out ∧
      Canon out ∧ decode out = R0P.valueReconstruct10 (fun i => FIv_NativeArray.value view i.val) := by
  have hsize : view.val.length = 16 := view.property
  let headSlice : Slice NQ := ⟨view.val.take 9,by have := Usize.cMax_bound_concrete.1; simp only [List.length_take,hsize]; omega⟩
  have hp : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice NQ)) view ⟨9#usize⟩ = ok headSlice := by
    simp only [core.array.Array.index,core.array.Array.index,core.ops.index.IndexSlice,
      core.slice.index.SliceIndexRangeToUsizeSlice,core.slice.index.Slice.index,
      core.slice.index.SliceIndexRangeToUsizeSlice.index]
    split
    · rfl
    · rename_i h
      change ¬ (9#usize).val ≤ view.val.length at h
      have hv : (9#usize).val = 9 := rfl
      omega
  obtain ⟨seed,hs,slot⟩ := NDE_RowBridge.read_total view 9#usize (by decide)
  have hseed : Canon seed := hc seed (List.mem_of_getElem? slot)
  have hpre : ∀ x ∈ headSlice.val, Canon x := by
    intro x hx
    exact hc x (List.mem_of_mem_take hx)
  obtain ⟨out,run,hco⟩ := fold_total headSlice.val headSlice.property seed () hpre hseed
  have returned : FIq_Native.pool_v1.pair_forest_semantic_terminal.reconstruct_10 view = ok out := by
    unfold FIq_Native.pool_v1.pair_forest_semantic_terminal.reconstruct_10
    rw [hp]
    simp only [bind_tc_ok]
    change (do let q ← Array.index_usize view 9#usize; fold ⟨headSlice,0⟩ q ()) = ok out
    rw [hs,bind_tc_ok]
    exact run
  exact ⟨out,returned,FIx_ReconstructMeaning.value view out hc returned⟩

#print axioms fold_total
#print axioms source
end NDE_ReconstructTotal
end
