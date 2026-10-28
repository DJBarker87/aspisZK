import RPv_JFy_Steps
import RPv_FIx_ReconstructTraversal
import RPv_FIx_ReconstructSliceValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGa_Reconstruct
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
open FIx_ReconstructTraversal (fold slice)
open FIx_ReconstructStep (Capture callback)

theorem cell (c : Capture) (acc bit : field.QM31) (ha : Canon acc) (hb : Canon bit) :
    ∃ out, callback.call_mut c (acc,bit)=ok (out,c) ∧ Canon out := by
  obtain ⟨d,hd,hdc,_⟩ := FIv_PreparedTotal.add acc acc ha ha
  obtain ⟨out,ho,hoc,_⟩ := FIv_PreparedTotal.add d bit hdc hb
  refine ⟨out,?_,hoc⟩
  change (do let d ← field.QM31.add acc acc
             let out ← field.QM31.add d bit
             ok (out,c))=ok (out,c)
  rw [hd,bind_tc_ok,ho,bind_tc_ok]
#print axioms cell

theorem folded (xs : List field.QM31) (bound : xs.length≤Usize.max) (acc : field.QM31) (c : Capture)
    (hc : ∀ x∈xs,Canon x) (ha : Canon acc) :
    ∃ out,fold ⟨slice xs bound,0⟩ acc c=ok out ∧ Canon out := by
  induction xs using List.reverseRecOn generalizing acc with
  | nil => exact ⟨acc,FIx_ReconstructTraversal.nil acc c,ha⟩
  | append_singleton xs x ih =>
    obtain ⟨next,hn,hnc⟩ := cell c acc x ha (hc x (by simp))
    obtain ⟨out,ho,hoc⟩ := ih (by have h:=bound; simp only [List.length_append,List.length_singleton] at h; omega)
      next (by intro y hy;exact hc y (by simp [hy])) hnc
    refine ⟨out,?_,hoc⟩
    rw [FIx_ReconstructTraversal.append,hn,bind_tc_ok]
    exact ho
#print axioms folded

@[step] theorem source (a : Array field.QM31 16#usize) (ha : canonical a) :
    pool_v1.pair_forest_semantic_terminal.reconstruct_10 a ⦃ out => Canon out ⦄ := by
  have spec : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice field.QM31)) a ⟨9#usize⟩
      ⦃ s => s.val=a.val.take 9 ⦄ := by
    step*
    simpa [List.slice] using s_post1
  obtain ⟨s,hs,hsv⟩ := WP.spec_imp_exists spec
  obtain ⟨q,hq,hqc⟩ := JFy_ArrayTotal.read a 9#usize (by decide) ha
  obtain ⟨out,ho,hoc⟩ := folded s.val s.property q ()
    (by intro x hx;rw [hsv] at hx;exact ha x (List.mem_of_mem_take hx)) hqc
  have run : pool_v1.pair_forest_semantic_terminal.reconstruct_10 a=ok out := by
    unfold pool_v1.pair_forest_semantic_terminal.reconstruct_10
    rw [hs,bind_tc_ok]
    change (do let q ← Array.index_usize a 9#usize
               fold ⟨s,0⟩ q ())=ok out
    rw [hq,bind_tc_ok]
    exact ho
  rw [run]
  exact hoc
#print axioms source
end AspisR1.JGa_Reconstruct
end
