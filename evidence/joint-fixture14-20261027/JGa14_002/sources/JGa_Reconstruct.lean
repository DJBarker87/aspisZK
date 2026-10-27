import JFy_Steps
import FIx_ReconstructTraversal
import FIx_ReconstructSliceValue
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
  unfold callback pool_v1.pair_forest_semantic_terminal.reconstruct_10.closure.Insts.CoreOpsFunctionFnMutPairQM31SharedQM31QM31.call_mut
  rw [hd,bind_tc_ok,ho,bind_tc_ok]
#print axioms cell

theorem folded (xs : List field.QM31) (bound : xs.length≤Usize.max) (acc : field.QM31) (c : Capture)
    (hc : ∀ x∈xs,Canon x) (ha : Canon acc) :
    ∃ out,fold ⟨slice xs bound,0⟩ acc c=ok out ∧ Canon out := by
  induction xs using List.reverseRecOn generalizing acc with
  | nil => exact ⟨acc,FIx_ReconstructTraversal.nil acc c,ha⟩
  | append_singleton xs x ih =>
    obtain ⟨next,hn,hnc⟩ := cell c acc x ha (hc x (by simp))
    obtain ⟨out,ho,hoc⟩ := ih (by simpa using Nat.le_trans (List.length_le_length_append_left xs [x]) bound)
      next (by intro y hy;exact hc y (by simp [hy])) hnc
    refine ⟨out,?_,hoc⟩
    rw [FIx_ReconstructTraversal.append,hn,bind_tc_ok]
    exact ho
#print axioms folded

@[step] theorem source (a : Array field.QM31 16#usize) (ha : canonical a) :
    pool_v1.pair_forest_semantic_terminal.reconstruct_10 a ⦃ out => Canon out ⦄ := by
  unfold pool_v1.pair_forest_semantic_terminal.reconstruct_10
  step*
  rename_i s hs q hq
  apply exists_imp_spec
  apply folded
  · intro x hx
    have hh := FIx_ReconstructSlice.value a s hs
    rw [hh] at hx
    exact ha x (List.mem_of_mem_take hx)
  · assumption
#print axioms source
end AspisR1.JGa_Reconstruct
end
